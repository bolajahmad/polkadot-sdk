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

//! ERC20Permit pallet for signature-based approvals (EIP-2612).
//!
//! This pallet stores permit-related state (nonces) and provides EIP-712
//! signature verification for gasless approvals.

use frame_support::pallet_prelude::*;
use pallet_revive::precompiles::H160;
use sp_core::H256;

pub use pallet::*;

/// EIP-712 type hash for Permit
/// keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)")
pub const PERMIT_TYPEHASH: [u8; 32] = [
	0x6e, 0x71, 0xed, 0xae, 0x12, 0xb1, 0xb9, 0x7f, 0x4d, 0x1f, 0x60, 0x37, 0x0f, 0xef, 0x10, 0x10,
	0x5f, 0xa2, 0xfa, 0xae, 0x01, 0x03, 0xa2, 0xf0, 0x30, 0x85, 0xed, 0x5f, 0x78, 0xb4, 0x33, 0x92,
];

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The chain ID used in EIP-712 domain separator.
		#[pallet::constant]
		type ChainId: Get<u64>;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	/// Nonces for permit signatures.
	/// Mapping: (asset_index, owner_address) => nonce
	#[pallet::storage]
	pub type Nonces<T: Config> = StorageDoubleMap<
		_,
		Identity,
		u32, // asset index
		Identity,
		H160, // owner ethereum address
		u64,  // nonce
		ValueQuery,
	>;

	/// Cached domain separator for EIP-712.
	/// This is computed once and reused for efficiency.
	#[pallet::storage]
	pub type CachedDomainSeparator<T: Config> = StorageValue<_, H256, OptionQuery>;

	impl<T: Config> Pallet<T> {
		/// Get the current nonce for an owner on a specific asset.
		pub fn nonce(asset_index: u32, owner: &H160) -> u64 {
			Nonces::<T>::get(asset_index, owner)
		}

		/// Increment the nonce for an owner on a specific asset.
		/// Returns the new nonce value.
		pub fn increment_nonce(asset_index: u32, owner: &H160) -> u64 {
			Nonces::<T>::mutate(asset_index, owner, |nonce| {
				*nonce = nonce.saturating_add(1);
				*nonce
			})
		}

		/// Get or compute the EIP-712 domain separator.
		pub fn domain_separator() -> H256 {
			if let Some(cached) = CachedDomainSeparator::<T>::get() {
				return cached;
			}

			let separator = Self::compute_domain_separator();
			CachedDomainSeparator::<T>::put(separator);
			separator
		}

		/// Compute the EIP-712 domain separator.
		/// DOMAIN_SEPARATOR = keccak256(abi.encode(
		///   keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
		///   keccak256("Asset Permit"),
		///   keccak256("1"),
		///   chainId,
		///   address(this)
		/// ))
		fn compute_domain_separator() -> H256 {
			use alloc::vec::Vec;
			use sp_io::hashing::keccak_256;

			// EIP712Domain typehash
			let domain_typehash = keccak_256(
				b"EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)",
			);

			let name_hash = keccak_256(b"Asset Permit");
			let version_hash = keccak_256(b"1");
			let chain_id = T::ChainId::get();

			// In a precompile context, verifyingContract would be the precompile address
			// For now, we use zero address as a placeholder
			let verifying_contract = H160::zero();

			// Encode: typehash || name_hash || version_hash || chainId || verifyingContract
			let mut data = Vec::with_capacity(160);
			data.extend_from_slice(&domain_typehash);
			data.extend_from_slice(&name_hash);
			data.extend_from_slice(&version_hash);
			// Pad chain_id to 32 bytes (big-endian)
			data.extend_from_slice(&[0u8; 24]);
			data.extend_from_slice(&chain_id.to_be_bytes());
			// Pad address to 32 bytes
			data.extend_from_slice(&[0u8; 12]);
			data.extend_from_slice(verifying_contract.as_bytes());

			H256(keccak_256(&data))
		}

		/// Compute the EIP-712 struct hash for a permit.
		/// structHash = keccak256(abi.encode(
		///   PERMIT_TYPEHASH,
		///   owner,
		///   spender,
		///   value,
		///   nonce,
		///   deadline
		/// ))
		pub fn permit_struct_hash(
			owner: &H160,
			spender: &H160,
			value: &[u8; 32], // U256 as bytes
			nonce: u64,
			deadline: &[u8; 32], // U256 as bytes
		) -> H256 {
			use alloc::vec::Vec;
			use sp_io::hashing::keccak_256;

			let mut data = Vec::with_capacity(192);
			data.extend_from_slice(&PERMIT_TYPEHASH);
			// owner (padded to 32 bytes)
			data.extend_from_slice(&[0u8; 12]);
			data.extend_from_slice(owner.as_bytes());
			// spender (padded to 32 bytes)
			data.extend_from_slice(&[0u8; 12]);
			data.extend_from_slice(spender.as_bytes());
			// value (already 32 bytes)
			data.extend_from_slice(value);
			// nonce (padded to 32 bytes)
			data.extend_from_slice(&[0u8; 24]);
			data.extend_from_slice(&nonce.to_be_bytes());
			// deadline (already 32 bytes)
			data.extend_from_slice(deadline);

			H256(keccak_256(&data))
		}

		/// Compute the final EIP-712 digest to be signed.
		/// digest = keccak256("\x19\x01" || domainSeparator || structHash)
		pub fn permit_digest(
			owner: &H160,
			spender: &H160,
			value: &[u8; 32],
			nonce: u64,
			deadline: &[u8; 32],
		) -> [u8; 32] {
			use alloc::vec::Vec;
			use sp_io::hashing::keccak_256;

			let domain_separator = Self::domain_separator();
			let struct_hash = Self::permit_struct_hash(owner, spender, value, nonce, deadline);

			let mut data = Vec::with_capacity(66);
			data.extend_from_slice(&[0x19, 0x01]);
			data.extend_from_slice(domain_separator.as_bytes());
			data.extend_from_slice(struct_hash.as_bytes());

			keccak_256(&data)
		}

		/// Recover the signer address from an ECDSA signature.
		/// Returns Ok(address) if the signature is valid, Err otherwise.
		pub fn ecrecover(
			digest: &[u8; 32],
			v: u8,
			r: &[u8; 32],
			s: &[u8; 32],
		) -> Result<H160, ()> {
			use sp_io::crypto::secp256k1_ecdsa_recover;
			use sp_io::hashing::keccak_256;

			// Convert v to recovery_id (Ethereum v is 27 or 28, recovery_id is 0 or 1)
			let recovery_id = v.checked_sub(27).ok_or(())?;
			if recovery_id > 1 {
				return Err(());
			}

			// Build signature in format expected by secp256k1_ecdsa_recover: [r, s, recovery_id]
			let mut sig = [0u8; 65];
			sig[0..32].copy_from_slice(r);
			sig[32..64].copy_from_slice(s);
			sig[64] = recovery_id;

			// Recover uncompressed public key (64 bytes)
			let pubkey = secp256k1_ecdsa_recover(&sig, digest).map_err(|_| ())?;

			// Convert public key to Ethereum address: keccak256(pubkey)[12..]
			let hash = keccak_256(&pubkey);
			let mut address = H160::zero();
			address.0.copy_from_slice(&hash[12..]);

			Ok(address)
		}

		/// Verify a permit signature.
		/// Returns Ok(()) if valid, Err(()) otherwise.
		pub fn verify_permit(
			asset_index: u32,
			owner: &H160,
			spender: &H160,
			value: &[u8; 32],
			deadline: &[u8; 32],
			v: u8,
			r: &[u8; 32],
			s: &[u8; 32],
		) -> Result<(), &'static str> {
			let nonce = Self::nonce(asset_index, owner);
			let digest = Self::permit_digest(owner, spender, value, nonce, deadline);

			let recovered = Self::ecrecover(&digest, v, r, s).map_err(|_| "Invalid signature")?;

			if &recovered != owner {
				return Err("Signer mismatch");
			}

			Ok(())
		}
	}
}
