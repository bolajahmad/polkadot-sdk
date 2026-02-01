// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use cumulus_primitives_core::ParaId;
use frame_support::{derive_impl, parameter_types};
use sp_runtime::BuildStorage;

type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test {
		System: frame_system,
		Subscriber: crate,
	}
);

#[derive_impl(frame_system::config_preludes::TestDefaultConfig)]
impl frame_system::Config for Test {
	type Block = Block;
}

// Test handler that records calls
parameter_types! {
	pub static ReceivedData: Vec<(ParaId, SubscribedKey, Vec<u8>, TtlState)> = vec![];
	pub static TestSubscriptions: Vec<(ParaId, Vec<SubscribedKey>)> = vec![];
}

pub struct TestHandler;
impl SubscriptionHandler for TestHandler {
	fn subscriptions() -> (Vec<(ParaId, Vec<SubscribedKey>)>, Weight) {
		(TestSubscriptions::get(), Weight::zero())
	}

	fn on_data_updated(
		publisher: ParaId,
		key: SubscribedKey,
		value: Vec<u8>,
		ttl_state: TtlState,
	) -> Weight {
		ReceivedData::mutate(|d| d.push((publisher, key, value, ttl_state)));
		Weight::zero()
	}
}

parameter_types! {
	pub const MaxPublishers: u32 = 100;
	pub const MaxTrieDepth: u32 = 8;
	pub const MaxCachedNodeSize: u32 = 512;
}

impl crate::Config for Test {
	type SubscriptionHandler = TestHandler;
	type WeightInfo = ();
	type MaxPublishers = MaxPublishers;
	type MaxTrieDepth = MaxTrieDepth;
	type MaxCachedNodeSize = MaxCachedNodeSize;
}

pub fn new_test_ext() -> sp_io::TestExternalities {
	let t = frame_system::GenesisConfig::<Test>::default().build_storage().unwrap();
	t.into()
}
