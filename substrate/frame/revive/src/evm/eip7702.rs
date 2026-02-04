// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! EIP-7702: Set EOA Account Code implementation
//!
//! This module implements the authorization processing for EIP-7702, which allows
//! Externally Owned Accounts (EOAs) to temporarily set code in their account via
//! authorization tuples attached to transactions.

use crate::{
	address::AddressMapper,
	evm::api::{recover_eth_address_from_message, AuthorizationListEntry},
	storage::AccountInfo,
	Config, LOG_TARGET,
};
use alloc::vec::Vec;
use sp_core::{H160, U256};
use sp_runtime::SaturatedConversion;

/// EIP-7702: Magic value for authorization signature message
pub const EIP7702_MAGIC: u8 = 0x05;

/// Process a list of EIP-7702 authorization tuples
///
/// # Parameters
/// - `authorization_list`: List of authorization tuples to process
/// - `chain_id`: Current chain ID
///
/// # Returns
/// Returns the number of authorizations that created new accounts.
///
/// # Note
/// This function does NOT charge the meter. The caller should account for the
/// authorization list weight via pre-dispatch and refund based on the number
/// of authorizations that did not create new accounts.
pub fn process_authorizations<T: Config>(
	authorization_list: &[AuthorizationListEntry],
	chain_id: U256,
) -> u32 {
	let mut new_account_count = 0u32;

	for auth in authorization_list.iter() {
		let Some((authority, is_new_account)) = validate_authorization::<T>(auth, chain_id) else {
			continue;
		};
		if is_new_account {
			new_account_count = new_account_count.saturating_add(1);
		}

		apply_delegation::<T>(&authority, auth.address);
	}

	new_account_count
}

/// Validate a single authorization tuple
///
/// Returns the authority address and whether it's a new account if validation succeeds,
/// None otherwise. This is exposed for benchmarking purposes.
pub(crate) fn validate_authorization<T: Config>(
	auth: &AuthorizationListEntry,
	chain_id: U256,
) -> Option<(H160, bool)> {
	if !auth.chain_id.is_zero() && auth.chain_id != chain_id {
		log::debug!(target: LOG_TARGET, "Invalid chain_id in authorization: expected {chain_id:?} or 0, got {:?}", auth.chain_id);
		return None;
	}

	let Ok(authority) = recover_authority(auth) else {
		log::debug!(target: LOG_TARGET, "Failed to recover authority from signature");
		return None;
	};
	let account_id = T::AddressMapper::to_account_id(&authority);

	let current_nonce: u64 = frame_system::Pallet::<T>::account_nonce(&account_id).saturated_into();
	let Ok::<u64, _>(expected_nonce) = auth.nonce.try_into() else {
		log::debug!(target: LOG_TARGET, "Authorization nonce too large: {:?}", auth.nonce);
		return None;
	};

	if current_nonce != expected_nonce {
		log::debug!(target: LOG_TARGET, "Nonce mismatch for {authority:?}: expected {expected_nonce:?}, got {current_nonce:?}");
		return None;
	}

	// Verify account is not a contract (but delegated accounts are allowed)
	if AccountInfo::<T>::is_contract(&authority) {
		log::debug!(target: LOG_TARGET, "Account {authority:?} has non-delegation code");
		return None;
	}

	let is_new_account = !frame_system::Account::<T>::contains_key(&account_id);
	Some((authority, is_new_account))
}

/// Apply a delegation for a single authority
///
/// This is exposed for benchmarking purposes.
pub(crate) fn apply_delegation<T: Config>(authority: &H160, target_address: H160) {
	if target_address.is_zero() {
		AccountInfo::<T>::clear_delegation(authority);
	} else {
		if let Err(e) = AccountInfo::<T>::set_delegation(authority, target_address) {
			log::debug!(target: LOG_TARGET, "Failed to set delegation for {authority:?}: {e:?}");
			return;
		}
	}

	frame_system::Pallet::<T>::inc_account_nonce(&T::AddressMapper::to_account_id(authority));
}

/// Recover the authority address from an authorization signature
///
/// Implements the EIP-7702 signature recovery:
/// - Message = keccak(MAGIC || rlp([chain_id, address, nonce]))
fn recover_authority(auth: &AuthorizationListEntry) -> Result<H160, ()> {
	let mut message = Vec::new();
	message.push(EIP7702_MAGIC);
	message.extend_from_slice(&auth.rlp_encode_unsigned());
	recover_eth_address_from_message(&message, &auth.signature())
}

/// Sign an authorization entry
///
/// This is a helper function for benchmarks and tests.
///
/// # Parameters
/// - `signing_key`: The k256 signing key to sign with
/// - `chain_id`: Chain ID for the authorization
/// - `address`: Target address to delegate to
/// - `nonce`: Nonce for the authorization
#[cfg(feature = "runtime-benchmarks")]
pub fn sign_authorization(
	signing_key: &k256::ecdsa::SigningKey,
	chain_id: U256,
	address: H160,
	nonce: U256,
) -> AuthorizationListEntry {
	let unsigned = AuthorizationListEntry { chain_id, address, nonce, ..Default::default() };
	let mut message = Vec::new();
	message.push(EIP7702_MAGIC);
	message.extend_from_slice(&unsigned.rlp_encode_unsigned());

	let hash = sp_core::keccak_256(&message);
	let (signature, recovery_id) =
		signing_key.sign_prehash_recoverable(&hash).expect("signing succeeds");

	AuthorizationListEntry {
		chain_id,
		address,
		nonce,
		y_parity: U256::from(recovery_id.to_byte()),
		r: U256::from_big_endian(&signature.r().to_bytes()),
		s: U256::from_big_endian(&signature.s().to_bytes()),
	}
}
