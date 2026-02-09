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
	Config, ExecConfig, Pallet, LOG_TARGET,
};
use alloc::vec::Vec;
use frame_support::traits::fungible::Inspect;
use sp_core::{Get, H160, U256};
use sp_runtime::SaturatedConversion;

/// EIP-7702: Magic value for authorization signature message
pub const EIP7702_MAGIC: u8 = 0x05;

/// Result of processing EIP-7702 authorization tuples.
#[derive(Default, Debug, PartialEq, Eq)]
pub struct AuthorizationResult {
	/// Number of authorizations that created new accounts.
	pub new_accounts: u32,
	/// Number of authorizations that applied to existing accounts.
	pub existing_accounts: u32,
}

/// Process a list of EIP-7702 authorization tuples.
///
/// For new accounts the ED is charged from `origin` via [`Pallet::charge_deposit`].
/// The caller should account for the authorization list weight via pre-dispatch
/// and refund based on the number of authorizations that did not create new accounts.
pub fn process_authorizations<T: Config>(
	authorization_list: &[AuthorizationListEntry],
	origin: &T::AccountId,
	exec_config: &ExecConfig<T>,
) -> Result<AuthorizationResult, sp_runtime::DispatchError> {
	let chain_id = U256::from(T::ChainId::get());
	let ed = <T::Currency as Inspect<T::AccountId>>::minimum_balance();
	let mut result = AuthorizationResult::default();

	for auth in authorization_list.iter() {
		if !auth.chain_id.is_zero() && auth.chain_id != chain_id {
			log::debug!(target: LOG_TARGET, "Invalid chain_id in authorization: expected {chain_id:?} or 0, got {:?}", auth.chain_id);
			continue;
		}

		let Ok(authority) = recover_authority(auth) else {
			log::debug!(target: LOG_TARGET, "Failed to recover authority from signature");
			continue;
		};
		let account_id = T::AddressMapper::to_account_id(&authority);

		let current_nonce: u64 =
			frame_system::Pallet::<T>::account_nonce(&account_id).saturated_into();
		let Ok::<u64, _>(expected_nonce) = auth.nonce.try_into() else {
			log::debug!(target: LOG_TARGET, "Authorization nonce too large: {:?}", auth.nonce);
			continue;
		};

		if current_nonce != expected_nonce {
			log::debug!(target: LOG_TARGET, "Nonce mismatch for {authority:?}: expected {expected_nonce:?}, got {current_nonce:?}");
			continue;
		}

		if AccountInfo::<T>::is_contract(&authority) {
			log::debug!(target: LOG_TARGET, "Account {authority:?} has non-delegation code");
			continue;
		}

		if !frame_system::Account::<T>::contains_key(&account_id) {
			Pallet::<T>::charge_deposit(None, origin, &account_id, ed, exec_config)?;
			result.new_accounts = result.new_accounts.saturating_add(1);
		} else {
			result.existing_accounts = result.existing_accounts.saturating_add(1);
		}

		// Apply delegation
		if auth.address.is_zero() {
			AccountInfo::<T>::clear_delegation(&authority);
		} else {
			if let Err(e) = AccountInfo::<T>::set_delegation(&authority, auth.address) {
				log::debug!(target: LOG_TARGET, "Failed to set delegation for {authority:?}: {e:?}");
				continue;
			}
		}

		frame_system::Pallet::<T>::inc_account_nonce(&account_id);
	}

	Ok(result)
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
#[cfg(feature = "runtime-benchmarks")]
pub fn sign_authorization(
	pair: &sp_core::ecdsa::Pair,
	chain_id: U256,
	address: H160,
	nonce: U256,
) -> AuthorizationListEntry {
	let unsigned = AuthorizationListEntry { chain_id, address, nonce, ..Default::default() };
	let mut message = Vec::new();
	message.push(EIP7702_MAGIC);
	message.extend_from_slice(&unsigned.rlp_encode_unsigned());

	let hash = sp_core::keccak_256(&message);
	let sig = pair.sign_prehashed(&hash);

	AuthorizationListEntry {
		chain_id,
		address,
		nonce,
		y_parity: U256::from(sig.0[64]),
		r: U256::from_big_endian(&sig.0[..32]),
		s: U256::from_big_endian(&sig.0[32..64]),
	}
}

/// Derive the Ethereum address from a signing key.
///
/// This is a helper function for benchmarks and tests.
#[cfg(feature = "runtime-benchmarks")]
pub fn eth_address(pair: &sp_core::ecdsa::Pair) -> H160 {
	let msg = [0u8; 32];
	let sig = pair.sign_prehashed(&msg);
	let pubkey = sp_io::crypto::secp256k1_ecdsa_recover(&sig.0, &msg)
		.ok()
		.expect("valid signature; qed");
	H160::from_slice(&sp_core::keccak_256(&pubkey)[12..])
}
