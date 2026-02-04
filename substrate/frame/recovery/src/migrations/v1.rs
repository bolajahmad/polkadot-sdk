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
//! This migration transforms the old storage format to the new format:
//! - `Recoverable` -> `FriendGroups` (with sensible defaults for new fields)
//! - `ActiveRecoveries` -> cleared (structure incompatible, deposits returned)
//! - `Proxy` -> `Inheritor` (mapping inverted)

extern crate alloc;

use super::{v0, PALLET_MIGRATIONS_ID};
#[cfg(feature = "try-runtime")]
use alloc::vec::Vec;
use crate::{pallet, Pallet};
use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	migrations::{MigrationId, SteppedMigration, SteppedMigrationError},
	pallet_prelude::PhantomData,
	traits::{Consideration, Get, ReservableCurrency},
	weights::WeightMeter,
	BoundedVec,
};

/// Cursor for tracking migration progress across the three old storage items.
#[derive(Encode, Decode, MaxEncodedLen, Clone, PartialEq, Eq, Debug)]
pub enum MigrationCursor<AccountId: MaxEncodedLen> {
	/// Migrating `Recoverable` storage to `FriendGroups`.
	Recoverable(Option<AccountId>),
	/// Migrating `ActiveRecoveries` storage (clearing, deposits returned).
	ActiveRecoveries(Option<(AccountId, AccountId)>),
	/// Migrating `Proxy` storage to `Inheritor`.
	Proxy(Option<AccountId>),
}

/// Multi-block migration from v0 to v1.
///
/// This migration:
/// 1. Converts `Recoverable` entries to `FriendGroups` with sensible defaults
/// 2. Clears `ActiveRecoveries` and returns deposits (structure incompatible)
/// 3. Converts `Proxy` entries to `Inheritor` (inverts the mapping)
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
						// Unreserve the old deposit
						let _ = <T as v0::MigrationConfig>::Currency::unreserve(&account, config.deposit);

						// Convert to v1 FriendGroup with defaults:
						// - inheritor: the account itself (user should update this)
						// - inheritance_order: 0
						// - cancel_delay: same as delay_period
						let cancel_delay = config.delay_period;
						let friend_group = config.into_v1_friend_group(
							account.clone(),
							0, // inheritance_order
							cancel_delay,
						);

						// Try to create new v1 storage entry with consideration ticket
						if let Ok(friend_groups) =
							BoundedVec::try_from(alloc::vec![friend_group])
						{
							let footprint = Pallet::<T>::friend_group_footprint(&friend_groups);
							if let Ok(ticket) =
								T::FriendGroupsConsideration::new(&account, footprint)
							{
								pallet::FriendGroups::<T>::insert(
									&account,
									(friend_groups, ticket),
								);
							}
							// If ticket creation fails, entry is skipped (deposit already returned)
						}

						v0::Recoverable::<T>::remove(&account);
						cursor = MigrationCursor::Recoverable(Some(account));
					} else {
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
						// Can't migrate ActiveRecoveries - structure is incompatible
						// Just unreserve the deposit and remove
						let _ = <T as v0::MigrationConfig>::Currency::unreserve(&rescuer, recovery.deposit);
						v0::ActiveRecoveries::<T>::remove(&lost, &rescuer);
						cursor = MigrationCursor::ActiveRecoveries(Some((lost, rescuer)));
					} else {
						cursor = MigrationCursor::Proxy(None);
					}
				},
				MigrationCursor::Proxy(last_key) => {
					let mut iter = if let Some(ref key) = last_key {
						v0::Proxy::<T>::iter_from(v0::Proxy::<T>::hashed_key_for(key))
					} else {
						v0::Proxy::<T>::iter()
					};

					if let Some((rescuer, lost)) = iter.next() {
						// Decrement the old consumer reference
						let _ = frame_system::Pallet::<T>::dec_consumers(&rescuer);

						// Convert to v1 Inheritor (note: mapping is inverted)
						// v0: Proxy[rescuer] = lost (rescuer can control lost)
						// v1: Inheritor[lost] = (order, inheritor, ticket)
						let inheritor = rescuer.clone();
						let inheritance_order = 0u32;

						// Create inheritor ticket
						if let Ok(ticket) = Pallet::<T>::inheritor_ticket(&inheritor) {
							pallet::Inheritor::<T>::insert(
								&lost,
								(inheritance_order, inheritor, ticket),
							);
						}
						// If ticket creation fails, entry is skipped

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

		let (recoverable_count, _active_recoveries_count, proxy_count) =
			<(u32, u32, u32)>::decode(&mut &state[..])
				.expect("Failed to decode pre_upgrade state");

		// All old storage should be cleared
		assert_eq!(v0::Recoverable::<T>::iter().count(), 0);
		assert_eq!(v0::ActiveRecoveries::<T>::iter().count(), 0);
		assert_eq!(v0::Proxy::<T>::iter().count(), 0);

		// New storage should be populated
		let friend_groups_count = pallet::FriendGroups::<T>::iter().count() as u32;
		let inheritor_count = pallet::Inheritor::<T>::iter().count() as u32;

		log::info!(
			target: "runtime::recovery",
			"MigrateV0ToV1: post_upgrade - FriendGroups: {}, Inheritor: {}",
			friend_groups_count,
			inheritor_count,
		);

		// FriendGroups should have same count as Recoverable (unless some failed)
		assert!(friend_groups_count <= recoverable_count);
		// Inheritor should have same count as Proxy (unless some failed)
		assert!(inheritor_count <= proxy_count);

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::{v0, MigrateV0ToV1};
	use crate::{
		mock::{new_test_ext, Balances, Test, ALICE, BOB, CHARLIE, DAVE, EVE},
		pallet,
	};
	use frame_support::{
		migrations::SteppedMigration,
		traits::{Currency, ReservableCurrency},
		weights::WeightMeter,
		BoundedVec,
	};

	type T = Test;

	fn friends(accounts: &[u64]) -> v0::FriendsOf<T> {
		let mut f: Vec<u64> = accounts.to_vec();
		f.sort();
		BoundedVec::try_from(f).unwrap()
	}

	fn run_migration() {
		let mut cursor = None;
		loop {
			let mut meter = WeightMeter::new();
			match MigrateV0ToV1::<T>::step(cursor, &mut meter) {
				Ok(None) => break,
				Ok(Some(c)) => cursor = Some(c),
				Err(e) => panic!("Migration failed: {:?}", e),
			}
		}
	}

	#[test]
	fn migration_works() {
		new_test_ext().execute_with(|| {
			let config_deposit = 50u128;
			let recovery_deposit = 100u128;

			// === Setup v0 storage ===

			// 1. Recoverable configs for ALICE and BOB
			v0::Recoverable::<T>::insert(
				ALICE,
				v0::RecoveryConfig {
					delay_period: 10u64,
					deposit: config_deposit,
					friends: friends(&[BOB, CHARLIE]),
					threshold: 2,
				},
			);
			Balances::reserve(&ALICE, config_deposit).unwrap();

			v0::Recoverable::<T>::insert(
				BOB,
				v0::RecoveryConfig {
					delay_period: 5u64,
					deposit: config_deposit,
					friends: friends(&[ALICE, CHARLIE]),
					threshold: 1,
				},
			);
			Balances::reserve(&BOB, config_deposit).unwrap();

			// 2. Active recovery: CHARLIE trying to recover ALICE
			v0::ActiveRecoveries::<T>::insert(
				ALICE,
				CHARLIE,
				v0::ActiveRecovery {
					created: 1u64,
					deposit: recovery_deposit,
					friends: friends(&[BOB]),
				},
			);
			Balances::reserve(&CHARLIE, recovery_deposit).unwrap();

			// 3. Proxy: DAVE has recovered EVE's account
			v0::Proxy::<T>::insert(DAVE, EVE);
			frame_system::Pallet::<T>::inc_consumers(&DAVE).unwrap();

			// === Verify v0 state before migration ===
			assert_eq!(v0::Recoverable::<T>::iter().count(), 2);
			assert_eq!(v0::ActiveRecoveries::<T>::iter().count(), 1);
			assert_eq!(v0::Proxy::<T>::iter().count(), 1);
			assert_eq!(Balances::reserved_balance(ALICE), config_deposit);
			assert_eq!(Balances::reserved_balance(BOB), config_deposit);
			assert_eq!(Balances::reserved_balance(CHARLIE), recovery_deposit);
			assert_eq!(frame_system::Pallet::<T>::consumers(&DAVE), 1);

			// === Run migration ===
			run_migration();

			// === Verify v0 storage is cleared ===
			assert_eq!(v0::Recoverable::<T>::iter().count(), 0);
			assert_eq!(v0::ActiveRecoveries::<T>::iter().count(), 0);
			assert_eq!(v0::Proxy::<T>::iter().count(), 0);

			// === Verify v1 storage is populated ===

			// FriendGroups should have entries for ALICE and BOB
			assert_eq!(pallet::FriendGroups::<T>::iter().count(), 2);

			// Check ALICE's migrated FriendGroups
			let (alice_groups, _ticket) = pallet::FriendGroups::<T>::get(ALICE).unwrap();
			assert_eq!(alice_groups.len(), 1);
			let alice_fg = &alice_groups[0];
			assert_eq!(alice_fg.friends.len(), 2);
			assert!(alice_fg.friends.contains(&BOB));
			assert!(alice_fg.friends.contains(&CHARLIE));
			assert_eq!(alice_fg.friends_needed, 2);
			assert_eq!(alice_fg.inheritance_delay, 10);
			assert_eq!(alice_fg.inheritor, ALICE); // defaults to self
			assert_eq!(alice_fg.inheritance_order, 0);

			// Check BOB's migrated FriendGroups
			let (bob_groups, _ticket) = pallet::FriendGroups::<T>::get(BOB).unwrap();
			assert_eq!(bob_groups.len(), 1);
			let bob_fg = &bob_groups[0];
			assert_eq!(bob_fg.friends_needed, 1);
			assert_eq!(bob_fg.inheritance_delay, 5);

			// Inheritor should have entry for EVE (lost) -> DAVE (inheritor)
			assert_eq!(pallet::Inheritor::<T>::iter().count(), 1);
			let (order, inheritor, _ticket) = pallet::Inheritor::<T>::get(EVE).unwrap();
			assert_eq!(inheritor, DAVE);
			assert_eq!(order, 0);

			// === Verify deposits ===
			// CHARLIE's recovery deposit should be fully unreserved (ActiveRecoveries cleared)
			assert_eq!(Balances::reserved_balance(CHARLIE), 0);
		});
	}
}
