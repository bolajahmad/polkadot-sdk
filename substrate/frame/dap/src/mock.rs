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

//! Test mock for the DAP pallet.

use crate::{self as pallet_dap, Config};
use sp_runtime::{traits::IdentityLookup, BuildStorage};
use frame_support::{
	derive_impl, parameter_types, sp_runtime::traits::AccountIdConversion, PalletId,
};

type Block = frame_system::mocking::MockBlock<Test>;
type AccountId = u128;

frame_support::construct_runtime!(
	pub enum Test {
		System: frame_system,
		Balances: pallet_balances,
		Dap: pallet_dap,
	}
);

#[derive_impl(frame_system::config_preludes::TestDefaultConfig)]
impl frame_system::Config for Test {
	type Block = Block;
	type AccountId = AccountId;
	type Lookup = IdentityLookup<Self::AccountId>;
	type AccountData = pallet_balances::AccountData<u64>;
}

#[derive_impl(pallet_balances::config_preludes::TestDefaultConfig)]
impl pallet_balances::Config for Test {
	type AccountStore = System;
	type ExistentialDeposit = ExistentialDeposit;
}

parameter_types! {
	pub const DapPalletId: PalletId = PalletId(*b"dap/buff");
	pub const ExistentialDeposit: u64 = 10;
}

/// Simple test EraPayout implementation.
///
/// Returns total inflation of 100. The split is determined by BudgetConfig.
pub struct TestEraPayout;
impl sp_staking::EraPayoutV2<u64> for TestEraPayout {
	fn era_payout(_total_staked: u64, _total_issuance: u64, _era_duration_millis: u64) -> u64 {
		// Return total inflation of 100
		100
	}
}

impl Config for Test {
	type Currency = Balances;
	type PalletId = DapPalletId;
	type EraPayout = TestEraPayout;
	type BudgetOrigin = frame_system::EnsureRoot<AccountId>;
}

pub fn new_test_ext(fund_buffer: bool) -> sp_io::TestExternalities {
	let mut balances = vec![(1, 100), (2, 200), (3, 300)];

	if fund_buffer {
		let buffer: u64 = DapPalletId::get().into_account_truncating();
		balances.push((buffer, ExistentialDeposit::get()));
	}

	let mut t = frame_system::GenesisConfig::<Test>::default().build_storage().unwrap();
	pallet_balances::GenesisConfig::<Test> { balances, ..Default::default() }
		.assimilate_storage(&mut t)
		.unwrap();
	t.into()
}
