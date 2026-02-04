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

//! Test for CurrentEra vs ActiveEra mismatch bug
//!
//! After PR #10311, there's a window where CurrentEra advances before ActiveEra,
//! causing nomination pools to think unbondings are withdrawable when staking
//! pallet hasn't actually withdrawn them yet.

#![cfg(test)]

use crate::mock::*;
use frame_support::assert_ok;
use pallet_nomination_pools::{PoolMembers, SubPoolsStorage};
use pallet_staking_async::{ActiveEra, CurrentEra, Ledger};

/// This test reproduces the bug where a pool member loses funds due to CurrentEra/ActiveEra mismatch.
///
/// ## Bug Scenario (After PR #10311):
/// 1. Pools uses CurrentEra to check if unbondings are withdrawable
/// 2. Staking uses ActiveEra to determine which chunks to actually withdraw
/// 3. During the mismatch window: CurrentEra = N, ActiveEra = N-1
///
/// ## The Bug:
/// - Real pools have multiple members with unbondings at different eras
/// - Previous successful withdrawals leave funds in the pool's `unclaimed_withdrawals`
/// - When a victim withdraws during the mismatch:
///   - Pools dissolves their points (thinks era is ready based on CurrentEra)
///   - The amount gets capped by `transferable_balance`
///   - Withdrawal succeeds using OTHER members' unclaimed funds
///   - Victim's actual staking chunk is never withdrawn (based on ActiveEra)
///   - Result: Points destroyed, funds still locked = PERMANENT LOSS
///
/// ## Real Incident (Asset Hub Polkadot, Block 11465558):
/// - Member had 18,555 DOT unbonding
/// - Pool had 674 DOT in unclaimed_withdrawals (from other members)
/// - Member received 1.24 DOT (from unclaimed)
/// - Member lost 18,553 DOT (chunk still in staking)
#[test]
fn current_era_active_era_mismatch_causes_fund_loss() {
	new_test_ext().execute_with(|| {
		// Accounts (all start with 100 tokens from test setup)
		let alice = 10;   // Pool creator
		let bob = 20;     // First member - creates unclaimed_withdrawals
		let charlie = 30; // Victim - loses funds due to bug

		let bonding_duration = BondingDuration::get(); // 3 eras

		// GIVEN

		// Alice creates a pool
		assert_ok!(Pools::create(RuntimeOrigin::signed(alice), 50, alice, alice, alice));
		assert_ok!(Pools::nominate(RuntimeOrigin::signed(alice), 1, vec![1, 2, 3]));

		// Start at era 0
		CurrentEra::<Runtime>::put(0);
		ActiveEra::<Runtime>::put(pallet_staking_async::ActiveEraInfo {
			index: 0,
			start: None,
		});

		// Bob joins the pool and unbonds (will unlock at era 3)
		assert_ok!(Pools::join(RuntimeOrigin::signed(bob), 20, 1));
		assert_ok!(Pools::unbond(RuntimeOrigin::signed(bob), bob, 20));

		// Advance one era so charlie has a different unlock era
		CurrentEra::<Runtime>::put(1);
		ActiveEra::<Runtime>::put(pallet_staking_async::ActiveEraInfo {
			index: 1,
			start: None,
		});

		// Charlie joins and unbonds (will unlock at era 4)
		assert_ok!(Pools::join(RuntimeOrigin::signed(charlie), 40, 1));
		assert_ok!(Pools::unbond(RuntimeOrigin::signed(charlie), charlie, 40));

		let charlie_unlock_era = 1 + bonding_duration; // Era 4

		// Verify charlie's unbonding is set up correctly
		let charlie_member = PoolMembers::<Runtime>::get(charlie).unwrap();
		assert_eq!(
			charlie_member.unbonding_eras.get(&charlie_unlock_era),
			Some(&40),
			"Charlie should have 40 points unbonding at era {}", charlie_unlock_era
		);

		// Bob successfully withdraws
		// Advance to era 3 (bob's unlock era) with eras ALIGNED
		CurrentEra::<Runtime>::put(3);
		ActiveEra::<Runtime>::put(pallet_staking_async::ActiveEraInfo {
			index: 3,
			start: None,
		});

		// Bob withdraws successfully - this creates unclaimed_withdrawals in the pool
		assert_ok!(Pools::withdraw_unbonded(RuntimeOrigin::signed(bob), bob, 0));

		// Verify bob got his funds back
		assert_eq!(
			Balances::free_balance(bob),
			100, // Started with 100, joined with 20, withdrew 20 = 100
			"Bob should have received his full withdrawal"
		);

		// -- Create Era Mismatch

		// Advance to charlie's unlock era (4) but with CurrentEra ahead of ActiveEra
		CurrentEra::<Runtime>::put(charlie_unlock_era);     // Era 4
		ActiveEra::<Runtime>::put(pallet_staking_async::ActiveEraInfo {
			index: charlie_unlock_era - 1, // Era 3
			start: None,
		});

		// Get state before charlie's withdrawal
		let charlie_balance_before = Balances::free_balance(charlie);
		let pool_account = Pools::generate_bonded_account(1);
		let ledger_before = Ledger::<Runtime>::get(&pool_account).unwrap();

		// Find charlie's unbonding chunk in staking ledger
		let charlie_chunk_before = ledger_before
			.unlocking
			.iter()
			.find(|chunk| chunk.era == charlie_unlock_era)
			.expect("Charlie's unbonding chunk should exist in staking ledger");
		assert_eq!(
			charlie_chunk_before.value, 40,
			"Charlie's chunk should be 40 tokens"
		);

		// Get SubPools state before withdrawal
		let sub_pools_before = SubPoolsStorage::<Runtime>::get(1).unwrap();
		let charlie_unbond_pool = sub_pools_before.with_era.get(&charlie_unlock_era).unwrap();
		assert_eq!(
			charlie_unbond_pool.points, 40,
			"UnbondPool should have 40 points for charlie"
		);
		assert_eq!(
			charlie_unbond_pool.balance, 40,
			"UnbondPool should have 40 balance (1:1 ratio)"
		);


		// WHEN: Charlie tries to withdraw
		// According to pools (uses CurrentEra=4) => WITHDRAWABLE
		// According to staking (uses ActiveEra=3): era 4 chunks not WITHDRAWABLE yet
		let withdraw_result = Pools::withdraw_unbonded(RuntimeOrigin::signed(charlie), charlie, 0);

		// THEN: Charlie lost points

		// withdraw succeeds in theory
		assert!(withdraw_result.is_ok());

		let expected_charlie_received = 40;
		let charlie_balance_after = Balances::free_balance(charlie);
		let actual_charlie_received = charlie_balance_after - charlie_balance_before;


		// Check if charlie's points were dissolved
		let charlie_after = PoolMembers::<Runtime>::get(charlie);
		let points_dissolved = charlie_after
			.as_ref()
			.map(|m| !m.unbonding_eras.contains_key(&charlie_unlock_era))
			.unwrap_or(true);

		assert!(points_dissolved);

		// Check if charlie's chunk is still in staking ledger
		let ledger_after = Ledger::<Runtime>::get(&pool_account).unwrap();
		let charlie_chunk_still_exists = ledger_after
			.unlocking
			.iter()
			.any(|chunk| chunk.era == charlie_unlock_era);

		assert!(charlie_chunk_still_exists);

		// Charlie should get back expected funds
		assert_eq!(expected_charlie_received, actual_charlie_received);
	});
}
