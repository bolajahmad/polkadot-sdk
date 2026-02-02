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

use frame_system::pallet_prelude::AccountIdFor;
use sp_runtime::DispatchError;

use crate::{BalanceOf, Config, Pallet, PotentialRenewalId, RelayBlockNumberOf};

// TODO: Extend the documentation.

/// Trait representig generic market logic.
///
/// The assumptions for this generic market are:
/// - Every order will either create a bid or will be resolved immediately.
/// - There're two types of orders: bulk coretime purchase and bulk coretime renewal.
/// - Coretime regions are fungible.
pub trait Market<Balance, RelayBlockNumber, AccountId> {
	type Error: Into<DispatchError>;
	/// Unique ID assigned to every bid.
	type BidId;

	/// Place an order for one bulk coretime region purchase.
	///
	/// This method may or may not create a bid, according to the market rules.
	///
	/// - `since_timeslice_start` - amount of blocks passed since the current timeslice start
	/// - `price` - maximum price which the buyer is willing to pay (or None if it's defined by the
	///   market itself)
	/// - `state` - market state, the caller is responsible for storing it
	fn place_order(
		since_timeslice_start: RelayBlockNumber,
		who: &AccountId,
		// TODO: Don't we want to specify the price every time?
		price: Option<Balance>,
	) -> Result<OrderResult<Balance, Self::BidId>, Self::Error>;

	/// Place an order for bulk coretime renewal.
	///
	/// This method may or may not create a bid, according to the market rules.
	///
	/// - `since_timeslice_start` - amount of blocks passed since the current timeslice start
	/// - `buying_price` - price which was paid for this region the last time it was sold
	/// - `state` - market state, the caller is responsible for storing it
	fn place_renewal_order(
		since_timeslice_start: RelayBlockNumber,
		who: AccountId,
		renewal: PotentialRenewalId,
		buying_price: Balance,
	) -> Result<RenewalOrderResult<Balance, Self::BidId>, Self::Error>;

	/// Close the bid given its `BidId`.
	///
	/// If the market logic allows creating the bids this method allows to close any bids (either
	/// forcefully if `maybe_check_owner` is `None` or checking the bid owner if it's `Some`).
	fn close_bid(id: Self::BidId, maybe_check_owner: Option<AccountId>) -> Result<(), Self::Error>;

	/// Logic that gets called in `on_initialize` hook.
	fn tick(
		since_timeslice_start: RelayBlockNumber,
	) -> Result<Vec<TickAction<AccountId, Balance, Self::BidId>>, Self::Error>;
}

pub enum OrderResult<Balance, BidId> {
	BidPlaced { id: BidId, bid_price: Balance },
	Sold { price: Balance },
}

pub enum RenewalOrderResult<Balance, BidId> {
	BidPlaced { id: BidId, bid_price: Balance },
	Sold { price: Balance },
}

pub enum TickAction<AccountId, Balance, BidId> {
	SellRegion { who: AccountId, refund: Balance },
	RenewRegion { who: AccountId, renewal_id: PotentialRenewalId, refund: Balance },
	CloseBid { id: BidId, amount: Balance },
}

impl<T: Config> Market<BalanceOf<T>, RelayBlockNumberOf<T>, AccountIdFor<T>> for Pallet<T> {
	type Error = DispatchError;
	type BidId = ();

	fn place_order(
		since_timeslice_start: RelayBlockNumberOf<T>,
		who: &AccountIdFor<T>,
		price: Option<BalanceOf<T>>,
	) -> Result<OrderResult<BalanceOf<T>, Self::BidId>, Self::Error> {
		todo!()
	}

	fn place_renewal_order(
		since_timeslice_start: RelayBlockNumberOf<T>,
		who: AccountIdFor<T>,
		renewal: PotentialRenewalId,
		buying_price: BalanceOf<T>,
	) -> Result<RenewalOrderResult<BalanceOf<T>, Self::BidId>, Self::Error> {
		todo!()
	}

	fn close_bid(
		id: Self::BidId,
		maybe_check_owner: Option<AccountIdFor<T>>,
	) -> Result<(), Self::Error> {
		todo!()
	}

	fn tick(
		since_timeslice_start: RelayBlockNumberOf<T>,
	) -> Result<Vec<TickAction<AccountIdFor<T>, BalanceOf<T>, Self::BidId>>, Self::Error> {
		todo!()
	}
}
