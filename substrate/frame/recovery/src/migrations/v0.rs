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

//! V0 storage definitions for the recovery pallet.
//!
//! These represent the old storage layout before the v1 migration.

use crate::InheritanceOrder;
use codec::{Decode, Encode, MaxEncodedLen};
use frame::traits::BlockNumberProvider;
use frame_support::{
	storage_alias,
	traits::{Currency, ReservableCurrency},
	Blake2_128Concat, BoundedVec, Twox64Concat,
};
use scale_info::TypeInfo;

/// Migration config - extends the new pallet Config with types needed for migration.
pub trait MigrationConfig: crate::pallet::Config {
	/// The currency type used in v0.
	/// Must implement ReservableCurrency for unreserving deposits.
	/// The Balance type must match the new pallet's Balance type.
	type Currency: ReservableCurrency<Self::AccountId, Balance = crate::BalanceOf<Self>>;
}

/// Old balance type for v0 storage.
pub type BalanceOf<T> =
	<<T as MigrationConfig>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

/// Old block number type from provider.
pub type BlockNumberFromProviderOf<T> =
	<<T as crate::pallet::Config>::BlockNumberProvider as BlockNumberProvider>::BlockNumber;

/// Old friends bounded vec type.
/// Uses MaxFriendsPerConfig from the new pallet Config (assumes same as old MaxFriends).
pub type FriendsOf<T> =
	BoundedVec<<T as frame_system::Config>::AccountId, <T as crate::pallet::Config>::MaxFriendsPerConfig>;

/// Old recovery configuration structure from v0.
#[derive(Clone, Eq, PartialEq, Encode, Decode, Default, TypeInfo, MaxEncodedLen)]
pub struct RecoveryConfig<BlockNumber, Balance, Friends> {
	/// The minimum number of blocks since the start of the recovery process before the
	/// account can be recovered.
	pub delay_period: BlockNumber,
	/// The amount held in reserve of the `depositor`,
	/// to be returned once this configuration is removed.
	pub deposit: Balance,
	/// The list of friends which can help recover an account. Always sorted.
	pub friends: Friends,
	/// The number of approving friends needed to recover an account.
	pub threshold: u16,
}

impl<BlockNumber, Balance, Friends> RecoveryConfig<BlockNumber, Balance, Friends> {
	/// Convert v0 RecoveryConfig to v1 FriendGroup.
	///
	/// Since v0 didn't have `inheritor`, `inheritance_order`, or `cancel_delay`,
	/// these must be provided as parameters.
	pub fn into_v1_friend_group<AccountId>(
		self,
		inheritor: AccountId,
		inheritance_order: InheritanceOrder,
		cancel_delay: BlockNumber,
	) -> crate::FriendGroup<BlockNumber, AccountId, Balance, Friends> {
		crate::FriendGroup {
			deposit: self.deposit,
			friends: self.friends,
			friends_needed: self.threshold as u32,
			inheritor,
			inheritance_delay: self.delay_period,
			inheritance_order,
			cancel_delay,
		}
	}
}

/// Old active recovery structure from v0.
#[derive(Clone, Eq, PartialEq, Encode, Decode, Default, TypeInfo, MaxEncodedLen)]
pub struct ActiveRecovery<BlockNumber, Balance, Friends> {
	/// The block number when the recovery process started.
	pub created: BlockNumber,
	/// The amount held in reserve of the `depositor`,
	/// to be returned once this recovery process is closed.
	pub deposit: Balance,
	/// The friends which have vouched so far. Always sorted.
	pub friends: Friends,
}

// Note: ActiveRecovery cannot be converted to v1 Attempt because the structures
// are fundamentally different. V0 tracks vouching friends as a list, v1 uses a
// bitfield and requires friend_group_index which doesn't exist in v0.

/// Old storage: The set of recoverable accounts and their recovery configuration.
#[storage_alias]
pub type Recoverable<T: MigrationConfig> = StorageMap<
	crate::pallet::Pallet<T>,
	Twox64Concat,
	<T as frame_system::Config>::AccountId,
	RecoveryConfig<BlockNumberFromProviderOf<T>, BalanceOf<T>, FriendsOf<T>>,
>;

/// Old storage: Active recovery attempts.
///
/// First account is the account to be recovered, and the second account
/// is the user trying to recover the account.
#[storage_alias]
pub type ActiveRecoveries<T: MigrationConfig> = StorageDoubleMap<
	crate::pallet::Pallet<T>,
	Twox64Concat,
	<T as frame_system::Config>::AccountId,
	Twox64Concat,
	<T as frame_system::Config>::AccountId,
	ActiveRecovery<BlockNumberFromProviderOf<T>, BalanceOf<T>, FriendsOf<T>>,
>;

/// Old storage: The list of allowed proxy accounts.
///
/// Map from the user who can access it to the recovered account.
#[storage_alias]
pub type Proxy<T: MigrationConfig> = StorageMap<
	crate::pallet::Pallet<T>,
	Blake2_128Concat,
	<T as frame_system::Config>::AccountId,
	<T as frame_system::Config>::AccountId,
>;
