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

//! Implementations of [`crate::oracle::Tally`].
//!
//! As it stands, it only has a basic (and not suggested) implementation that simply uses the
//! average. More advanced implementations can be written at the runtime level.

use crate::oracle::TallyOuterError;
use frame_system::pallet_prelude::BlockNumberFor;
use sp_runtime::{traits::Saturating, FixedPointNumber, FixedU128, Percent};

/// Simple implementation of [`crate::oracle::Tally`] that simply uses the average.
///
/// Always returns [`crate::oracle::TallyOuterError::YankVotes`] in the case of no votes.
///
/// Should only be used for testing.
pub struct SimpleAverage<T>(core::marker::PhantomData<T>);

impl<T: crate::oracle::Config> crate::oracle::Tally for SimpleAverage<T> {
	type AssetId = T::AssetId;
	type AccountId = T::AccountId;
	type BlockNumber = BlockNumberFor<T>;
	type Error = ();

	fn tally(
		_asset_id: Self::AssetId,
		votes: alloc::vec::Vec<(Self::AccountId, sp_runtime::FixedU128, Self::BlockNumber)>,
	) -> Result<(FixedU128, Percent), TallyOuterError<Self::Error>> {
		if votes.is_empty() {
			Err(TallyOuterError::YankVotes(()))
		} else {
			let count = FixedU128::saturating_from_integer(votes.len() as u32);
			let average = votes
				.into_iter()
				.map(|(_who, price, _produced_in)| price)
				.reduce(|acc, x| acc.saturating_add(x))
				.unwrap_or_default()
				.div(count);
			Ok((average, Percent::from_percent(100)))
		}
	}
}
