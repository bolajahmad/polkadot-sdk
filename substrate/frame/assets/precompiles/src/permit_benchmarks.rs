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

#![cfg(feature = "runtime-benchmarks")]

use crate::permit::{pallet::Config, Pallet};
use frame_benchmarking::v2::*;
use pallet_revive::precompiles::H160;
use sp_core::U256;

fn test_verifying_contract() -> H160 {
	H160::from_low_u64_be(0x1234_5678)
}

fn test_owner() -> H160 {
	H160::from_low_u64_be(0xABCD_EF01)
}

#[benchmarks]
mod benchmarks {
	use super::*;

	#[benchmark]
	fn nonces() {
		let verifying_contract = test_verifying_contract();
		let owner = test_owner();
		crate::permit::Nonces::<T>::insert(&verifying_contract, &owner, U256::from(42));

		let result;
		#[block]
		{
			result = Pallet::<T>::nonce(&verifying_contract, &owner);
		}
		assert_eq!(result, U256::from(42));
	}

	#[benchmark]
	fn domain_separator() {
		let verifying_contract = test_verifying_contract();

		let result;
		#[block]
		{
			result = Pallet::<T>::compute_domain_separator(&verifying_contract);
		}
		assert_ne!(result, sp_core::H256::zero());
	}

	#[benchmark]
	fn use_permit() {
		let verifying_contract = test_verifying_contract();
		let owner = test_owner();
		let spender = H160::from_low_u64_be(0x9876_5432);
		let value: [u8; 32] = U256::from(1000).to_big_endian();
		let deadline: [u8; 32] = U256::from(u64::MAX).to_big_endian();

		// Synthetic signature - valid format but won't verify
		let r: [u8; 32] = [
			0x9e, 0x9b, 0x5e, 0x0b, 0x89, 0x7f, 0x40, 0x5b, 0x7c, 0x3a, 0x8c, 0x6a, 0x5b, 0x3c,
			0x4d, 0x5e, 0x6f, 0x7a, 0x8b, 0x9c, 0x0a, 0x1b, 0x2c, 0x3d, 0x4e, 0x5f, 0x6a, 0x7b,
			0x8c, 0x9d, 0x0e, 0x1f,
		];
		let s: [u8; 32] = [
			0x1c, 0x2d, 0x3e, 0x4f, 0x5a, 0x6b, 0x7c, 0x8d, 0x9e, 0xaf, 0xb0, 0xc1, 0xd2, 0xe3,
			0xf4, 0x05, 0x16, 0x27, 0x38, 0x49, 0x5a, 0x6b, 0x7c, 0x8d, 0x9e, 0xaf, 0xb0, 0xc1,
			0xd2, 0xe3, 0xf4, 0x05,
		];
		let v = 27u8;

		#[block]
		{
			let _ = Pallet::<T>::use_permit(
				&verifying_contract,
				&owner,
				&spender,
				&value,
				&deadline,
				v,
				&r,
				&s,
			);
		}
	}

	impl_benchmark_test_suite!(Pallet, crate::mock::new_test_ext(), crate::mock::Test);
}
