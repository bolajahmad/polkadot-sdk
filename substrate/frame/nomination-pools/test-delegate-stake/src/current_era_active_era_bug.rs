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

#![cfg(test)]

use crate::mock::*;
use frame_support::{assert_ok, traits::fungible::Mutate};
use pallet_nomination_pools::PoolMembers;
use pallet_staking_async::{ActiveEra, CurrentEra, Ledger};

/// Reproduces bug where pool member loses funds due to CurrentEra/ActiveEra mismatch.
#[test]
fn current_era_active_era_mismatch_causes_fund_loss() {
	new_test_ext().execute_with(|| {
		let alice = 10;   // Pool creator
		let bob = 20;     // Member who creates unclaimed funds
		let charlie = 30; // Victim
		let dave = 40;    // Member whose funds remain unclaimed

		let bonding_duration = BondingDuration::get(); // 3 eras
		assert_eq!(bonding_duration, 3);

		// Fund accounts
		let _ = Balances::mint_into(&alice, 1000);
		let _ = Balances::mint_into(&bob, 1000);
		let _ = Balances::mint_into(&dave, 1000);
		let _ = Balances::mint_into(&charlie, 1000);

		// Alice creates pool
		assert_ok!(Pools::create(RuntimeOrigin::signed(alice), 200, alice, alice, alice));
		assert_ok!(Pools::nominate(RuntimeOrigin::signed(alice), 1, vec![1, 2, 3]));

		// Era 0
		CurrentEra::<Runtime>::put(0);
		ActiveEra::<Runtime>::put(pallet_staking_async::ActiveEraInfo {
			index: 0,
			start: None,
		});

		// Bob and Dave join and unbond for era 3
		assert_ok!(Pools::join(RuntimeOrigin::signed(bob), 100, 1));
		assert_ok!(Pools::unbond(RuntimeOrigin::signed(bob), bob, 100));

		assert_ok!(Pools::join(RuntimeOrigin::signed(dave), 100, 1));
		assert_ok!(Pools::unbond(RuntimeOrigin::signed(dave), dave, 100));

		let early_unlock_era = bonding_duration; // Era 3

		// Advance to era 3 with eras ALIGNED
		CurrentEra::<Runtime>::put(early_unlock_era);
		ActiveEra::<Runtime>::put(pallet_staking_async::ActiveEraInfo {
			index: early_unlock_era,
			start: None,
		});

		// Bob withdraws, which consolidates BOTH bob's and dave's chunks into unclaimed_withdrawals
		// Bob claims his 100, leaving dave's 100 in unclaimed_withdrawals
		assert_ok!(Pools::withdraw_unbonded(RuntimeOrigin::signed(bob), bob, 0));

		let pool_account = Pools::generate_bonded_account(1);
		let agent = pallet_delegated_staking::Agents::<Runtime>::get(&pool_account).unwrap();
		assert_eq!(agent.unclaimed_withdrawals, 100);

		// Charlie joins with 200 and unbonds 150 (unlocks at era 6)
		// Charlie should get 150, but will be capped to Dave's unclaimed 100
		assert_ok!(Pools::join(RuntimeOrigin::signed(charlie), 200, 1));
		assert_ok!(Pools::unbond(RuntimeOrigin::signed(charlie), charlie, 150));

		let charlie_unlock_era = early_unlock_era + bonding_duration; // Era 6

		// Verify charlie's 150 chunk exists in staking ledger
		let ledger_before = Ledger::<Runtime>::get(&pool_account).unwrap();
		let charlie_chunk = ledger_before
			.unlocking
			.iter()
			.find(|chunk| chunk.era == charlie_unlock_era);
		assert_eq!(charlie_chunk.unwrap().value, 150);

		// Create era mismatch: CurrentEra advances to 6, ActiveEra stays at 5
		CurrentEra::<Runtime>::put(charlie_unlock_era);
		ActiveEra::<Runtime>::put(pallet_staking_async::ActiveEraInfo {
			index: charlie_unlock_era - 1,
			start: None,
		});

		// Charlie withdraws during era mismatch
		let charlie_balance_before = Balances::free_balance(charlie);
		let result = Pools::withdraw_unbonded(RuntimeOrigin::signed(charlie), charlie, 0);
		let charlie_balance_after = Balances::free_balance(charlie);

		// Withdrawal succeeds but capped to Dave's unclaimed 100
		assert!(result.is_ok());
		let charlie_received = charlie_balance_after - charlie_balance_before;
		assert_eq!(charlie_received, 100, "Charlie gets capped to unclaimed funds");

		// BUG: All 150 points dissolved despite only receiving 100
		let charlie_after = PoolMembers::<Runtime>::get(charlie);
		let points_dissolved = charlie_after
			.as_ref()
			.map(|m| !m.unbonding_eras.contains_key(&charlie_unlock_era))
			.unwrap_or(true);
		assert!(points_dissolved, "BUG: All 150 points dissolved");

		// Charlie's 150 chunk still in staking ledger (staking uses ActiveEra)
		let ledger_after = Ledger::<Runtime>::get(&pool_account).unwrap();
		let chunk_after = ledger_after
			.unlocking
			.iter()
			.find(|chunk| chunk.era == charlie_unlock_era);
		assert_eq!(chunk_after.unwrap().value, 150, "BUG: Charlie's 150 still locked in staking");

		// 50 balance trapped: Charlie got 100, lost 150 points, but 150 still in staking
		let trapped = 150 - charlie_received;
		assert_eq!(trapped, 50, "50 balance trapped with no points to claim it");
	});
}
