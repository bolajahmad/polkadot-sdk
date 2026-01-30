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

//! Tests for DapCurrency wrapper: verifies that burn_from redirects to buffer.

use crate::{currency::DapCurrency, mock::*};
use frame_support::{
	assert_ok,
	traits::{
		fungible::{Inspect, Mutate},
		tokens::{Fortitude::Polite, Precision::Exact, Preservation::Expendable},
	},
};

type DapPallet = crate::Pallet<Test>;
type DapCurrencyWrapper = DapCurrency<Test>;

// ============================================================================
// Tests for DapCurrency::burn_from (redirects burns to DAP buffer)
// ============================================================================

#[test]
fn dap_currency_burn_from_redirects_to_buffer() {
	new_test_ext().execute_with(|| {
		// Given
		let buffer = DapPallet::buffer_account();
		let ed = <Balances as Inspect<_>>::minimum_balance();
		let initial_total = Balances::total_issuance();
		let initial_active = Balances::active_issuance();
		assert_eq!(Balances::free_balance(buffer), ed);

		// When: multiple burns from different accounts via DapCurrency
		assert_ok!(<DapCurrencyWrapper as Mutate<_>>::burn_from(&1, 30, Expendable, Exact, Polite));
		assert_ok!(<DapCurrencyWrapper as Mutate<_>>::burn_from(&2, 50, Expendable, Exact, Polite));
		assert_ok!(<DapCurrencyWrapper as Mutate<_>>::burn_from(
			&3, 100, Expendable, Exact, Polite
		));

		// Then: buffer accumulated all burns
		assert_eq!(Balances::free_balance(buffer), ed + 180);
		// And: total issuance unchanged (funds transferred, not destroyed)
		assert_eq!(Balances::total_issuance(), initial_total);
		// And: active issuance decreased (funds deactivated)
		assert_eq!(Balances::active_issuance(), initial_active - 180);
		// And: user balances updated
		assert_eq!(Balances::free_balance(1), 70);
		assert_eq!(Balances::free_balance(2), 150);
		assert_eq!(Balances::free_balance(3), 200);
	});
}

#[test]
fn dap_currency_burn_from_can_reap_account() {
	new_test_ext().execute_with(|| {
		// Given
		let buffer = DapPallet::buffer_account();
		let ed = <Balances as Inspect<_>>::minimum_balance();
		let initial_total = Balances::total_issuance();
		assert_eq!(Balances::free_balance(1), 100);

		// When: burn entire balance via DapCurrency (Expendable allows reaping)
		assert_ok!(<DapCurrencyWrapper as Mutate<_>>::burn_from(
			&1, 100, Expendable, Exact, Polite
		));

		// Then: account reaped
		assert_eq!(Balances::free_balance(1), 0);
		// And: buffer received funds
		assert_eq!(Balances::free_balance(buffer), ed + 100);
		// And: total issuance unchanged
		assert_eq!(Balances::total_issuance(), initial_total);
	});
}

#[test]
fn dap_currency_burn_from_respects_preservation() {
	use frame_support::{assert_noop, traits::tokens::Preservation::Preserve};
	use sp_runtime::TokenError;

	new_test_ext().execute_with(|| {
		// Given: user has 100
		assert_eq!(Balances::free_balance(1), 100);

		// When: try to burn all with Preserve via DapCurrency (should fail to keep account alive)
		let result = <DapCurrencyWrapper as Mutate<_>>::burn_from(&1, 100, Preserve, Exact, Polite);

		// Then: fails because it would kill the account
		assert_noop!(result, TokenError::FundsUnavailable);

		// And: can burn amount that keeps account alive
		let ed = <Balances as Inspect<_>>::minimum_balance();
		assert_ok!(<DapCurrencyWrapper as Mutate<_>>::burn_from(
			&1,
			100 - ed,
			Preserve,
			Exact,
			Polite
		));
		assert_eq!(Balances::free_balance(1), ed);
	});
}

// ============================================================================
// Tests verifying standard Balances::burn_from still reduces total issuance
// ============================================================================

#[test]
fn standard_balances_burn_from_reduces_total_issuance() {
	new_test_ext().execute_with(|| {
		// Given
		let initial_total = Balances::total_issuance();
		assert_eq!(Balances::free_balance(1), 100);

		// When: direct Balances::burn_from (not via DapCurrency wrapper)
		let burned = <Balances as Mutate<_>>::burn_from(&1, 50, Expendable, Exact, Polite);
		assert_ok!(burned);
		assert_eq!(burned.unwrap(), 50);

		// Then: total issuance REDUCED (standard burn behavior)
		assert_eq!(Balances::total_issuance(), initial_total - 50);
		// And: user balance decreased
		assert_eq!(Balances::free_balance(1), 50);
	});
}
