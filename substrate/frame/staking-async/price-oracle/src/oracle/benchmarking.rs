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

//! Benchmarking for pallet-price-oracle

use super::*;
use crate::oracle::{
	offchain::{Endpoint, Method, ParsingMethod},
	*,
};
use frame_benchmarking::v2::*;
use frame_support::pallet_prelude::*;
use sp_runtime::FixedU128;

/// Utilities for the benchmarking from the runtime.
///
/// If asset-id type supports `Default`, then `()` can be used.
pub trait BenchmarkHelper<T: Config> {
	/// A valid example asset-id.
	fn asset_id() -> T::AssetId;
}

impl<T: Config> BenchmarkHelper<T> for ()
where
	T::AssetId: Default,
{
	fn asset_id() -> T::AssetId {
		Default::default()
	}
}

#[benchmarks]
mod benchmarks {

	use frame_system::RawOrigin;

	use super::*;

	// On finalize hook benchmark. Is a function of the number of assets that we tally, and the
	// number of votes. Since the weight is registered on_finalize, there is no point in refunding,
	// so only want the worst case weight. The exact weight also depends on the implementation of
	// our tally.
	#[benchmark]
	fn on_finalize_per_asset() -> Result<(), BenchmarkError> {
		// register a new asset
		assert!(T::MaxVotesPerBlock::get() > 0, "MaxVotesPerBlock must be greater than 0");
		let asset_id = T::BenchmarkHelper::asset_id();
		let endpoints = vec![Endpoint {
			url: b"http://example.com/price".to_vec().try_into().unwrap(),
			method: Method::Get,
			headers: Default::default(),
			body: Default::default(),
			parsing_method: ParsingMethod::CryptoCompareFree,
			requires_api_key: false,
			confidence: Default::default(),
			deadline: Default::default(),
		}];
		let now = Pallet::<T>::local_block_number();
		let bounded = BoundedVec::<_, _>::try_from(endpoints).expect("endpoints should fit");
		StorageManager::<T>::register_asset(asset_id, bounded)?;

		// register maximum number of votes
		(0..T::MaxVotesPerBlock::get())
			.map(|idx| {
				StorageManager::<T>::add_vote(
					asset_id,
					frame_benchmarking::account::<T::AccountId>("voter", 0, idx),
					// TODO: using `let vote` in this macro messes things up... some bug in the
					// source.
					Vote { price: FixedU128::from_rational(idx as u128, 10), produced_in: now },
				)
			})
			.collect::<Result<Vec<_>, _>>()?;

		// ensure no previous price exists
		assert!(StorageManager::<T>::current_price(asset_id).is_none());

		// call on_finalize
		#[block]
		{
			Pallet::<T>::on_finalize(now);
		}

		// ensure tally ha happened.
		assert!(StorageManager::<T>::current_price(asset_id).is_some());
		Ok(())
	}

	#[benchmark]
	fn vote() -> Result<(), BenchmarkError> {
		// register a valid asset.
		let asset_id = T::BenchmarkHelper::asset_id();
		let endpoints = vec![Endpoint {
			url: b"http://example.com/price".to_vec().try_into().unwrap(),
			method: Method::Get,
			headers: Default::default(),
			body: Default::default(),
			parsing_method: ParsingMethod::CryptoCompareFree,
			requires_api_key: false,
			confidence: Default::default(),
			deadline: Default::default(),
		}];
		let bounded = BoundedVec::<_, _>::try_from(endpoints).expect("endpoints should fit");
		StorageManager::<T>::register_asset(asset_id, bounded)?;
		let now = Pallet::<T>::local_block_number();

		// grab a random account and register them as an authority.
		let authority = frame_benchmarking::account::<T::AccountId>("authority", 0, 0);
		Authorities::<T>::try_mutate(|a| a.try_insert(authority.clone(), One::one()))
			.map_err(|_| "TooManyAuthorities")?;

		#[block]
		{
			Pallet::<T>::vote(
				RawOrigin::Signed(authority).into(),
				asset_id,
				FixedU128::from_rational(1, 10),
				now,
			)?;
		}

		Ok(())
	}

	impl_benchmark_test_suite! {
		Pallet,
		crate::oracle::mock::ExtBuilder::default().empty().max_votes_per_block(10).build(),
		crate::oracle::mock::Runtime,
	}
}
