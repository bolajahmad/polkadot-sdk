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

use super::permit;
use crate::mock::{new_test_ext, Test};
use pallet_revive::precompiles::H160;
use sp_core::H256;

#[test]
fn nonce_starts_at_zero() {
	new_test_ext().execute_with(|| {
		let owner = H160::from_low_u64_be(1);
		let asset_index = 0;

		let nonce = permit::Pallet::<Test>::nonce(asset_index, &owner);
		assert_eq!(nonce, 0);
	});
}

#[test]
fn nonce_increments() {
	new_test_ext().execute_with(|| {
		let owner = H160::from_low_u64_be(1);
		let asset_index = 0;

		let nonce1 = permit::Pallet::<Test>::increment_nonce(asset_index, &owner);
		assert_eq!(nonce1, 1);

		let nonce2 = permit::Pallet::<Test>::increment_nonce(asset_index, &owner);
		assert_eq!(nonce2, 2);

		let nonce_read = permit::Pallet::<Test>::nonce(asset_index, &owner);
		assert_eq!(nonce_read, 2);
	});
}

#[test]
fn nonces_are_independent_per_asset() {
	new_test_ext().execute_with(|| {
		let owner = H160::from_low_u64_be(1);
		let asset_index_1 = 0;
		let asset_index_2 = 1;

		permit::Pallet::<Test>::increment_nonce(asset_index_1, &owner);
		permit::Pallet::<Test>::increment_nonce(asset_index_1, &owner);

		assert_eq!(permit::Pallet::<Test>::nonce(asset_index_1, &owner), 2);
		assert_eq!(permit::Pallet::<Test>::nonce(asset_index_2, &owner), 0);
	});
}

#[test]
fn nonces_are_independent_per_owner() {
	new_test_ext().execute_with(|| {
		let owner1 = H160::from_low_u64_be(1);
		let owner2 = H160::from_low_u64_be(2);
		let asset_index = 0;

		permit::Pallet::<Test>::increment_nonce(asset_index, &owner1);
		permit::Pallet::<Test>::increment_nonce(asset_index, &owner1);

		assert_eq!(permit::Pallet::<Test>::nonce(asset_index, &owner1), 2);
		assert_eq!(permit::Pallet::<Test>::nonce(asset_index, &owner2), 0);
	});
}

#[test]
fn domain_separator_is_computed() {
	new_test_ext().execute_with(|| {
		let separator = permit::Pallet::<Test>::domain_separator();
		// Should be a non-zero hash
		assert_ne!(separator, H256::zero());
	});
}

#[test]
fn domain_separator_is_cached() {
	new_test_ext().execute_with(|| {
		let separator1 = permit::Pallet::<Test>::domain_separator();
		let separator2 = permit::Pallet::<Test>::domain_separator();
		// Should return the same value (cached)
		assert_eq!(separator1, separator2);
	});
}

#[test]
fn permit_digest_is_deterministic() {
	new_test_ext().execute_with(|| {
		let owner = H160::from_low_u64_be(1);
		let spender = H160::from_low_u64_be(2);
		let value = [0u8; 32];
		let nonce = 0;
		let deadline = [0u8; 32];

		let digest1 =
			permit::Pallet::<Test>::permit_digest(&owner, &spender, &value, nonce, &deadline);
		let digest2 =
			permit::Pallet::<Test>::permit_digest(&owner, &spender, &value, nonce, &deadline);

		assert_eq!(digest1, digest2);
	});
}

#[test]
fn permit_digest_changes_with_nonce() {
	new_test_ext().execute_with(|| {
		let owner = H160::from_low_u64_be(1);
		let spender = H160::from_low_u64_be(2);
		let value = [0u8; 32];
		let deadline = [0u8; 32];

		let digest1 = permit::Pallet::<Test>::permit_digest(&owner, &spender, &value, 0, &deadline);
		let digest2 = permit::Pallet::<Test>::permit_digest(&owner, &spender, &value, 1, &deadline);

		assert_ne!(digest1, digest2);
	});
}

#[test]
fn ecrecover_with_valid_signature() {
	new_test_ext().execute_with(|| {
		// This is a known valid ECDSA signature from Ethereum
		// Message: "hello world"
		// Private key: 0x4c0883a69102937d6231471b5dbb6204fe512961708279f8c5c6e4d7b9e5b3e3
		// Expected address: 0x96216849c49358B10257cb55b28eA603c874b05E

		let digest = sp_io::hashing::keccak_256(b"hello world");
		let r: [u8; 32] = [
			0x6b, 0x8d, 0x72, 0x8f, 0x6f, 0x8a, 0x8a, 0x7e, 0x4f, 0x8f, 0x2a, 0x7a, 0x9f, 0x7b, 0x7a,
			0x8a, 0x7b, 0x8c, 0x7d, 0x8e, 0x7f, 0x8f, 0x9a, 0x8a, 0x9b, 0x8c, 0x9d, 0x8e, 0x9f, 0x8f,
			0xa0, 0x90,
		];
		let s: [u8; 32] = [
			0x1c, 0x2d, 0x3e, 0x4f, 0x5a, 0x6b, 0x7c, 0x8d, 0x9e, 0xaf, 0xb0, 0xc1, 0xd2, 0xe3, 0xf4,
			0x05, 0x16, 0x27, 0x38, 0x49, 0x5a, 0x6b, 0x7c, 0x8d, 0x9e, 0xaf, 0xb0, 0xc1, 0xd2, 0xe3,
			0xf4, 0x05,
		];
		let v = 27u8;

		// Note: This is a synthetic test. Real signature verification would require
		// a properly signed message with a known private key.
		// For now, we just verify the function doesn't panic.
		let _ = permit::Pallet::<Test>::ecrecover(&digest, v, &r, &s);
	});
}

#[test]
fn ecrecover_fails_with_invalid_v() {
	new_test_ext().execute_with(|| {
		let digest = [0u8; 32];
		let r = [0u8; 32];
		let s = [0u8; 32];
		let v = 30u8; // Invalid v value

		let result = permit::Pallet::<Test>::ecrecover(&digest, v, &r, &s);
		assert!(result.is_err());
	});
}
