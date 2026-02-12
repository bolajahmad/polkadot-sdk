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

//! # Multi-Block Migration v3
//!
//! Re-encode `AccountInfoOf` entries after merging the `Delegated` variant into `EOA`.

extern crate alloc;

use super::PALLET_MIGRATIONS_ID;
use crate::{AccountInfo, AccountInfoOf, Config, H160, storage::AccountType, weights::WeightInfo};
use frame_support::{
	migrations::{MigrationId, SteppedMigration, SteppedMigrationError},
	pallet_prelude::PhantomData,
	weights::WeightMeter,
};

#[cfg(feature = "try-runtime")]
use alloc::vec::Vec;

/// Old storage types as they exist on master (before EIP-7702 changes).
pub mod old {
	use super::Config;
	use crate::{H160, pallet::Pallet, storage::ContractInfo};
	use codec::{Decode, Encode, MaxEncodedLen};
	use frame_support::{CloneNoBound, DefaultNoBound, Identity, storage_alias};
	use scale_info::TypeInfo;

	#[derive(
		DefaultNoBound, Encode, Decode, CloneNoBound, PartialEq, Eq, Debug, TypeInfo, MaxEncodedLen,
	)]
	#[scale_info(skip_type_params(T))]
	pub enum AccountType<T: Config> {
		Contract(ContractInfo<T>),
		#[default]
		EOA,
	}

	#[derive(
		DefaultNoBound, Encode, Decode, CloneNoBound, PartialEq, Eq, Debug, TypeInfo, MaxEncodedLen,
	)]
	#[scale_info(skip_type_params(T))]
	pub struct AccountInfo<T: Config> {
		pub account_type: AccountType<T>,
		pub dust: u32,
	}

	#[storage_alias]
	pub type AccountInfoOf<T: Config> = StorageMap<Pallet<T>, Identity, H160, AccountInfo<T>>;
}

/// Migrates `AccountInfoOf` entries from the old two-variant `AccountType` (Contract, EOA)
/// to the new encoding where `EOA` carries optional `delegate_target` and `contract_info`.
pub struct Migration<T: Config>(PhantomData<T>);

impl<T: Config> SteppedMigration for Migration<T> {
	type Cursor = H160;
	type Identifier = MigrationId<17>;

	fn id() -> Self::Identifier {
		MigrationId { pallet_id: *PALLET_MIGRATIONS_ID, version_from: 2, version_to: 3 }
	}

	fn step(
		mut cursor: Option<Self::Cursor>,
		meter: &mut WeightMeter,
	) -> Result<Option<Self::Cursor>, SteppedMigrationError> {
		let required = <T as Config>::WeightInfo::v3_migration_step();
		if meter.remaining().any_lt(required) {
			return Err(SteppedMigrationError::InsufficientWeight { required });
		}

		loop {
			if meter.try_consume(required).is_err() {
				break;
			}

			let iter = if let Some(last_key) = cursor {
				old::AccountInfoOf::<T>::iter_from(old::AccountInfoOf::<T>::hashed_key_for(
					last_key,
				))
			} else {
				old::AccountInfoOf::<T>::iter()
			};

			if let Some((last_key, value)) = iter.into_iter().next() {
				let new_account_type = match value.account_type {
					old::AccountType::Contract(ci) => AccountType::Contract(ci),
					old::AccountType::EOA => {
						AccountType::EOA { delegate_target: None, contract_info: None }
					},
				};
				AccountInfoOf::<T>::insert(
					last_key,
					AccountInfo { account_type: new_account_type, dust: value.dust },
				);
				cursor = Some(last_key)
			} else {
				cursor = None;
				break;
			}
		}
		Ok(cursor)
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<Vec<u8>, frame_support::sp_runtime::TryRuntimeError> {
		use codec::Encode;
		Ok((old::AccountInfoOf::<T>::iter().count() as u32).encode())
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade(prev: Vec<u8>) -> Result<(), frame_support::sp_runtime::TryRuntimeError> {
		use codec::Decode;
		let prev_count = u32::decode(&mut &prev[..]).expect("pre_upgrade encoded a u32");
		assert_eq!(
			AccountInfoOf::<T>::iter().count() as u32,
			prev_count,
			"Migration v3: entry count mismatch"
		);
		Ok(())
	}
}

#[test]
fn migrate_to_v3() {
	use crate::{
		ContractInfo,
		tests::{ExtBuilder, Test},
	};

	ExtBuilder::default().genesis_config(None).build().execute_with(|| {
		let addr_eoa = H160::from([1u8; 20]);
		let addr_contract = H160::from([2u8; 20]);

		let ci = ContractInfo::new(&addr_contract, 1u32.into(), Default::default()).unwrap();

		old::AccountInfoOf::<Test>::insert(
			addr_eoa,
			old::AccountInfo { account_type: old::AccountType::EOA, dust: 42 },
		);
		old::AccountInfoOf::<Test>::insert(
			addr_contract,
			old::AccountInfo { account_type: old::AccountType::Contract(ci.clone()), dust: 0 },
		);

		// Run migration
		let mut cursor = None;
		let mut weight_meter = WeightMeter::new();
		while let Some(new_cursor) = Migration::<Test>::step(cursor, &mut weight_meter).unwrap() {
			cursor = Some(new_cursor);
		}

		assert_eq!(AccountInfoOf::<Test>::iter().count(), 2);

		// Check EOA preserved
		let eoa = AccountInfoOf::<Test>::get(addr_eoa).unwrap();
		assert_eq!(eoa.dust, 42);
		assert_eq!(
			eoa.account_type,
			AccountType::EOA { delegate_target: None, contract_info: None }
		);

		// Check Contract preserved
		let contract = AccountInfoOf::<Test>::get(addr_contract).unwrap();
		assert_eq!(contract.account_type, AccountType::Contract(ci));
	})
}
