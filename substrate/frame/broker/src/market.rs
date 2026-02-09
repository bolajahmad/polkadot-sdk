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

use core::cmp;
use frame_support::traits::tokens::Balance;
use frame_system::pallet_prelude::AccountIdFor;
use sp_arithmetic::FixedPointNumber;
use sp_runtime::{DispatchError, FixedU64, SaturatedConversion, Saturating};

use crate::{
	BalanceOf, Config, Configuration, Pallet, PotentialRenewalId, RelayBlockNumberOf, SaleInfo,
};

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
	/// - `price_limit` - maximum price which the buyer is willing to pay
	fn place_order(
		since_timeslice_start: RelayBlockNumber,
		who: &AccountId,
		price_limit: Balance,
	) -> Result<OrderResult<Balance, Self::BidId>, Self::Error>;

	/// Place an order for bulk coretime renewal.
	///
	/// This method may or may not create a bid, according to the market rules.
	///
	/// - `since_timeslice_start` - amount of blocks passed since the current timeslice start
	fn place_renewal_order(
		since_timeslice_start: RelayBlockNumber,
		who: &AccountId,
		renewal: PotentialRenewalId,
		recorded_price: Balance,
	) -> Result<RenewalOrderResult<Balance, Self::BidId>, Self::Error>;

	/// Close the bid given its `BidId`.
	///
	/// If the market logic allows creating the bids this method allows to close any bids (either
	/// forcefully if `maybe_check_owner` is `None` or checking the bid owner if it's `Some`).
	fn close_bid(
		id: Self::BidId,
		maybe_check_owner: Option<AccountId>,
	) -> Result<CloseBidResult<AccountId, Balance>, Self::Error>;

	/// Logic that gets called in `on_initialize` hook.
	fn tick(
		since_timeslice_start: RelayBlockNumber,
	) -> Vec<TickAction<AccountId, Balance, Self::BidId>>;
}

pub enum OrderResult<Balance, BidId> {
	BidPlaced { id: BidId, bid_price: Balance },
	Sold { price: Balance },
}

pub enum RenewalOrderResult<Balance, BidId> {
	BidPlaced { id: BidId, bid_price: Balance },
	Sold { price: Balance, next_renewal_price: Balance },
}

pub struct CloseBidResult<AccountId, Balance> {
	pub owner: AccountId,
	pub refund: Balance,
}
pub enum TickAction<AccountId, Balance, BidId> {
	SellRegion { who: AccountId, refund: Balance },
	RenewRegion { who: AccountId, renewal_id: PotentialRenewalId, refund: Balance },
	CloseBid { id: BidId, amount: Balance },
}

pub enum MarketError {
	NoSales,
	Overpriced,
	BidNotExist,
	Uninitialized,
}

// TODO: Proper conversion
impl From<MarketError> for DispatchError {
	fn from(value: MarketError) -> Self {
		DispatchError::Other("TODO")
	}
}

impl<T: Config> Market<BalanceOf<T>, RelayBlockNumberOf<T>, AccountIdFor<T>> for Pallet<T> {
	type Error = MarketError;
	/// Must be unique.
	type BidId = ();

	fn place_order(
		since_timeslice_start: RelayBlockNumberOf<T>,
		_who: &AccountIdFor<T>,
		price_limit: BalanceOf<T>,
	) -> Result<OrderResult<BalanceOf<T>, Self::BidId>, Self::Error> {
		let sell_price = sell_price::<T>(since_timeslice_start)?;

		if price_limit < sell_price {
			Err(MarketError::Overpriced)
		} else {
			Ok(OrderResult::Sold { price: sell_price })
		}
	}

	fn place_renewal_order(
		since_timeslice_start: RelayBlockNumberOf<T>,
		who: &AccountIdFor<T>,
		renewal: PotentialRenewalId,
		recorded_price: BalanceOf<T>,
	) -> Result<RenewalOrderResult<BalanceOf<T>, Self::BidId>, Self::Error> {
		// TODO: Store `config.renewal_bump` in the market config.
		let config = Configuration::<T>::get().ok_or(MarketError::Uninitialized)?;
		// TODO: Don't access main pallet storage here.
		let sale = SaleInfo::<T>::get().ok_or(MarketError::NoSales)?;

		let price_cap =
			cmp::max(recorded_price + config.renewal_bump * recorded_price, sale.end_price);
		let sell_price = sell_price::<T>(since_timeslice_start)?;
		let next_renewal_price = sell_price.min(price_cap);

		return Ok(RenewalOrderResult::Sold { price: recorded_price, next_renewal_price })
	}

	fn close_bid(
		id: Self::BidId,
		maybe_check_owner: Option<AccountIdFor<T>>,
	) -> Result<CloseBidResult<AccountIdFor<T>, BalanceOf<T>>, Self::Error> {
		Err(MarketError::BidNotExist)
	}

	fn tick(
		since_timeslice_start: RelayBlockNumberOf<T>,
	) -> Vec<TickAction<AccountIdFor<T>, BalanceOf<T>, Self::BidId>> {
		vec![]
	}
}

fn sell_price<T: Config>(
	since_timeslice_start: RelayBlockNumberOf<T>,
) -> Result<BalanceOf<T>, MarketError> {
	// TODO: Store this info in the dedicated storage item?
	let sale = SaleInfo::<T>::get().ok_or(MarketError::NoSales)?;

	let num = since_timeslice_start.min(sale.leadin_length).saturated_into();
	let through = FixedU64::from_rational(num, sale.leadin_length.saturated_into());
	Ok(leadin_factor_at(through).saturating_mul_int(sale.end_price))
}

fn leadin_factor_at(when: FixedU64) -> FixedU64 {
	if when <= FixedU64::from_rational(1, 2) {
		FixedU64::from(100).saturating_sub(when.saturating_mul(180.into()))
	} else {
		FixedU64::from(19).saturating_sub(when.saturating_mul(18.into()))
	}
}
