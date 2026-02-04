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

//! Multi-block migration from v0 to v1 for the recovery pallet.
//!
//! This migration transforms the old storage format to the new format and releases
//! any reserved deposits from the old system.

extern crate alloc;

use super::{v0, PALLET_MIGRATIONS_ID};
#[cfg(feature = "try-runtime")]
use alloc::vec::Vec;
use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	migrations::{MigrationId, SteppedMigration, SteppedMigrationError},
	pallet_prelude::PhantomData,
	traits::{Get, ReservableCurrency},
	weights::WeightMeter,
};

/// Cursor for tracking migration progress across the three old storage items.
#[derive(Encode, Decode, MaxEncodedLen, Clone, PartialEq, Eq, Debug)]
pub enum MigrationCursor<AccountId: MaxEncodedLen> {
	/// Migrating `Recoverable` storage.
	Recoverable(Option<AccountId>),
	/// Migrating `ActiveRecoveries` storage.
	ActiveRecoveries(Option<(AccountId, AccountId)>),
	/// Migrating `Proxy` storage.
	Proxy(Option<AccountId>),
}

/// Multi-block migration from v0 to v1.
///
/// This migration:
/// 1. Iterates through all `Recoverable` entries, unreserves deposits, and removes them
/// 2. Iterates through all `ActiveRecoveries` entries, unreserves deposits, and removes them
/// 3. Iterates through all `Proxy` entries, decrements consumers, and removes them
///
/// The v1 storage structure is completely different from v0 and cannot be automatically
/// populated from v0 data. Users will need to reconfigure their recovery settings using
/// the new pallet interface after the migration.
pub struct MigrateV0ToV1<T: v0::MigrationConfig>(PhantomData<T>);

impl<T: v0::MigrationConfig> SteppedMigration for MigrateV0ToV1<T> {
	type Cursor = MigrationCursor<T::AccountId>;
	type Identifier = MigrationId<16>;

	fn id() -> Self::Identifier {
		MigrationId { pallet_id: *PALLET_MIGRATIONS_ID, version_from: 0, version_to: 1 }
	}

	fn step(
		cursor: Option<Self::Cursor>,
		meter: &mut WeightMeter,
	) -> Result<Option<Self::Cursor>, SteppedMigrationError> {
		// Each step does: 1 storage read + 1 storage write + 1 unreserve operation.
		let required = T::DbWeight::get().reads_writes(2, 2);

		if meter.remaining().any_lt(required) {
			return Err(SteppedMigrationError::InsufficientWeight { required });
		}

		let mut cursor = cursor.unwrap_or(MigrationCursor::Recoverable(None));

		loop {
			if meter.try_consume(required).is_err() {
				break;
			}

			match cursor {
				MigrationCursor::Recoverable(last_key) => {
					let mut iter = if let Some(ref key) = last_key {
						v0::Recoverable::<T>::iter_from(v0::Recoverable::<T>::hashed_key_for(key))
					} else {
						v0::Recoverable::<T>::iter()
					};

					if let Some((account, config)) = iter.next() {
						// Unreserve the deposit held for the recovery config.
						let _ = T::OldCurrency::unreserve(&account, config.deposit);
						// Remove the old storage item.
						v0::Recoverable::<T>::remove(&account);
						cursor = MigrationCursor::Recoverable(Some(account));
					} else {
						// Move to next storage item.
						cursor = MigrationCursor::ActiveRecoveries(None);
					}
				},
				MigrationCursor::ActiveRecoveries(last_key) => {
					let mut iter = if let Some((ref lost, ref rescuer)) = last_key {
						v0::ActiveRecoveries::<T>::iter_from(
							v0::ActiveRecoveries::<T>::hashed_key_for(lost, rescuer),
						)
					} else {
						v0::ActiveRecoveries::<T>::iter()
					};

					if let Some((lost, rescuer, recovery)) = iter.next() {
						// Unreserve the deposit held by the rescuer.
						let _ = T::OldCurrency::unreserve(&rescuer, recovery.deposit);
						// Remove the old storage item.
						v0::ActiveRecoveries::<T>::remove(&lost, &rescuer);
						cursor = MigrationCursor::ActiveRecoveries(Some((lost, rescuer)));
					} else {
						// Move to next storage item.
						cursor = MigrationCursor::Proxy(None);
					}
				},
				MigrationCursor::Proxy(last_key) => {
					let mut iter = if let Some(ref key) = last_key {
						v0::Proxy::<T>::iter_from(v0::Proxy::<T>::hashed_key_for(key))
					} else {
						v0::Proxy::<T>::iter()
					};

					if let Some((rescuer, _lost)) = iter.next() {
						// Decrement the consumer reference that was added when claiming recovery.
						let _ = frame_system::Pallet::<T>::dec_consumers(&rescuer);
						// Remove the old storage item.
						v0::Proxy::<T>::remove(&rescuer);
						cursor = MigrationCursor::Proxy(Some(rescuer));
					} else {
						// Migration complete!
						return Ok(None);
					}
				},
			}
		}

		Ok(Some(cursor))
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<Vec<u8>, frame_support::sp_runtime::TryRuntimeError> {
		use codec::Encode;

		let recoverable_count = v0::Recoverable::<T>::iter().count() as u32;
		let active_recoveries_count = v0::ActiveRecoveries::<T>::iter().count() as u32;
		let proxy_count = v0::Proxy::<T>::iter().count() as u32;

		log::info!(
			target: "runtime::recovery",
			"MigrateV0ToV1: pre_upgrade - Recoverable: {}, ActiveRecoveries: {}, Proxy: {}",
			recoverable_count,
			active_recoveries_count,
			proxy_count,
		);

		Ok((recoverable_count, active_recoveries_count, proxy_count).encode())
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade(state: Vec<u8>) -> Result<(), frame_support::sp_runtime::TryRuntimeError> {
		use codec::Decode;

		let (recoverable_count, active_recoveries_count, proxy_count) =
			<(u32, u32, u32)>::decode(&mut &state[..])
				.expect("Failed to decode pre_upgrade state");

		// All old storage should be cleared.
		assert_eq!(
			v0::Recoverable::<T>::iter().count(),
			0,
			"Recoverable storage should be empty after migration"
		);
		assert_eq!(
			v0::ActiveRecoveries::<T>::iter().count(),
			0,
			"ActiveRecoveries storage should be empty after migration"
		);
		assert_eq!(
			v0::Proxy::<T>::iter().count(),
			0,
			"Proxy storage should be empty after migration"
		);

		log::info!(
			target: "runtime::recovery",
			"MigrateV0ToV1: post_upgrade - Cleared {} Recoverable, {} ActiveRecoveries, {} Proxy entries",
			recoverable_count,
			active_recoveries_count,
			proxy_count,
		);

		Ok(())
	}
}
