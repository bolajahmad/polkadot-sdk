// Copyright (C) Parity Technologies (UK) Ltd.
// This file is part of Cumulus.
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

#![cfg_attr(not(feature = "std"), no_std)]

//! Subscriber pallet for processing published data from relay chain state proofs.
//!
//! This pallet enables parachains to subscribe to data published by other parachains via the
//! relay chain's broadcaster pallet. It processes relay chain state proofs to extract published
//! data and delivers it to a configurable handler.
//!
//! ## Overview
//!
//! The pub-sub system works as follows:
//! 1. Publisher parachains store data in the relay chain via XCM `Publish` instructions
//! 2. The relay chain stores this data in per-publisher child tries
//! 3. Subscriber parachains include proofs of this data in their relay chain state proofs
//! 4. This pallet extracts and processes the published data from those proofs
//!
//! ## Subscription Pattern
//!
//! Implement the [`SubscriptionHandler`] trait to receive published data:
//!
//! ```ignore
//! impl SubscriptionHandler for MyHandler {
//!     fn subscriptions() -> (Vec<(ParaId, Vec<SubscribedKey>)>, Weight) {
//!         // Return list of (publisher_id, keys) to subscribe to
//!         (vec![(ParaId::from(1000), vec![subscribed_key!("my_key")])], Weight::zero())
//!     }
//!
//!     fn on_data_updated(publisher: ParaId, key: SubscribedKey, value: Vec<u8>, ttl: TtlState) -> Weight {
//!         // Handle the received data
//!         Weight::zero()
//!     }
//! }
//! ```
//!
//! Use the [`subscribed_key!`] macro for compile-time key hashing:
//! ```ignore
//! let key = subscribed_key!("my_data_key");  // Creates SubscribedKey from blake2_256 hash
//! ```
//!
//! ## TTL (Time-To-Live) Handling
//!
//! Published data includes TTL metadata via [`TtlState`]:
//! - [`TtlState::Infinite`]: Data never expires automatically
//! - [`TtlState::ValidFor(blocks)`]: Data expires after the specified number of blocks
//! - [`TtlState::TimedOut`]: Data has already expired
//!
//! Use [`compute_ttl_state`] to convert raw TTL values to state.
//!
//! ## Cache Management
//!
//! The pallet caches trie nodes in [`CachedTrieNodes`] storage to reduce proof sizes:
//! - First access populates the cache with trie nodes
//! - Subsequent accesses can skip unchanged subtrees
//! - Cache is automatically invalidated when trie structure changes
//!
//! Use [`Pallet::clear_publisher_cache`] to manually clear cache for a publisher.
//!
//! ## Publisher Disabling
//!
//! Publishers are automatically disabled if their trie exceeds [`Config::MaxTrieDepth`]:
//! - Disabled publishers are stored in [`DisabledPublishers`]
//! - See [`DisableReason`] for possible causes
//! - Re-enable via [`Pallet::enable_publisher`] (Root origin)
//!
//! ## Integration
//!
//! Configure with the parachain-system pallet:
//! ```ignore
//! impl cumulus_pallet_parachain_system::Config for Runtime {
//!     type RelayProofExtender = Subscriber;
//!     // ...
//! }
//! ```
//!
//! This pallet implements
//! [`RelayProofExtender`](cumulus_pallet_parachain_system::RelayProofExtender) to request and
//! process relay chain proofs containing published data.
//!
//! ## Processing Order
//!
//! Publishers are processed in priority order:
//! 1. System parachains (ParaId < 2000) are processed first
//! 2. Non-system parachains follow in ParaId order
//!
//! Processing respects weight budgets and uses cursor-based resumption across blocks.

extern crate alloc;

use alloc::{collections::btree_map::BTreeMap, vec::Vec};
use codec::{Decode, Encode, MaxEncodedLen};
use cumulus_pallet_parachain_system::{relay_state_snapshot::RelayChainStateProof, OnSystemEvent};
use cumulus_primitives_core::ParaId;
use frame_support::{
	defensive,
	pallet_prelude::*,
	storage::bounded_btree_map::BoundedBTreeMap,
	traits::{Get, StorageVersion},
	weights::Weight,
};
use polkadot_runtime_parachains::broadcaster::PublishedEntry;
use scale_info::TypeInfo;
use sp_core::H256;
use sp_runtime::SaturatedConversion;

pub use pallet::*;
pub use weights::{SubstrateWeight, WeightInfo};

/// Reason why a publisher was disabled.
#[derive(
	Clone,
	Copy,
	Debug,
	PartialEq,
	Eq,
	Encode,
	Decode,
	MaxEncodedLen,
	TypeInfo,
	codec::DecodeWithMemTracking,
)]
pub enum DisableReason {
	/// The publisher's trie exceeded the maximum allowed depth.
	TrieDepthExceeded,
}

/// TTL state for published data.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub enum TtlState {
	/// Data has infinite TTL (never expires automatically).
	Infinite,
	/// Data is valid for the specified number of remaining blocks.
	ValidFor(u32),
	/// Data has timed out (TTL expired).
	TimedOut,
}

/// A subscribed key wrapping a 32-byte hash.
#[derive(
	Clone,
	Copy,
	Debug,
	PartialEq,
	Eq,
	Encode,
	Decode,
	MaxEncodedLen,
	TypeInfo,
	Hash,
	codec::DecodeWithMemTracking,
)]
pub struct SubscribedKey(pub H256);

impl SubscribedKey {
	/// Create from a pre-computed hash.
	pub fn from_hash(hash: [u8; 32]) -> Self {
		Self(H256::from(hash))
	}

	/// Create from raw data by hashing with Blake2-256.
	pub fn from_data(data: &[u8]) -> Self {
		Self(H256::from(sp_crypto_hashing::blake2_256(data)))
	}

	/// Get the inner hash as bytes.
	pub fn as_bytes(&self) -> &[u8; 32] {
		self.0.as_fixed_bytes()
	}

	/// Get the inner H256.
	pub fn inner(&self) -> H256 {
		self.0
	}
}

impl From<[u8; 32]> for SubscribedKey {
	fn from(hash: [u8; 32]) -> Self {
		Self::from_hash(hash)
	}
}

impl From<H256> for SubscribedKey {
	fn from(hash: H256) -> Self {
		Self(hash)
	}
}

impl AsRef<[u8]> for SubscribedKey {
	fn as_ref(&self) -> &[u8] {
		self.0.as_bytes()
	}
}

/// Macro to create a `SubscribedKey` from a string literal at compile time.
///
/// Uses Blake2-256 hashing via `sp_crypto_hashing::blake2_256`.
///
/// # Example
/// ```ignore
/// let key = subscribed_key!("my_key");
/// ```
#[macro_export]
macro_rules! subscribed_key {
	($data:expr) => {
		$crate::SubscribedKey::from_hash(sp_crypto_hashing::blake2_256($data.as_bytes()))
	};
}

/// Compute TTL state from TTL value, insertion block, and current block.
///
/// - If `ttl == 0`, returns `TtlState::Infinite`.
/// - If `current_block >= when_inserted + ttl`, returns `TtlState::TimedOut`.
/// - Otherwise, returns `TtlState::ValidFor(remaining_blocks)`.
pub fn compute_ttl_state<BlockNumber: Into<u64> + Copy>(
	ttl: u32,
	when_inserted: BlockNumber,
	current_block: BlockNumber,
) -> TtlState {
	if ttl == 0 {
		return TtlState::Infinite;
	}

	let when_inserted: u64 = when_inserted.into();
	let current_block: u64 = current_block.into();
	let expiration = when_inserted.saturating_add(ttl as u64);

	if current_block >= expiration {
		TtlState::TimedOut
	} else {
		let remaining = expiration.saturating_sub(current_block);
		TtlState::ValidFor(remaining.min(u32::MAX as u64) as u32)
	}
}

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
#[cfg(test)]
mod mock;
#[cfg(any(test, feature = "runtime-benchmarks"))]
mod test_util;
#[cfg(test)]
mod tests;
pub mod weights;

/// Define subscriptions and handle received data.
pub trait SubscriptionHandler {
	/// List of subscriptions as (ParaId, keys) tuples.
	/// Returns (subscriptions, weight) where weight is the cost of computing the subscriptions.
	fn subscriptions() -> (Vec<(ParaId, Vec<SubscribedKey>)>, Weight);

	/// Called when subscribed data is updated.
	/// Returns the weight consumed by processing the data.
	fn on_data_updated(
		publisher: ParaId,
		key: SubscribedKey,
		value: Vec<u8>,
		ttl_state: TtlState,
	) -> Weight;
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_system::pallet_prelude::*;

	const STORAGE_VERSION: StorageVersion = StorageVersion::new(1);

	#[pallet::pallet]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Handler for defining subscriptions and processing received data.
		type SubscriptionHandler: SubscriptionHandler;
		/// Weight information for extrinsics and operations.
		type WeightInfo: WeightInfo;
		/// Maximum number of publishers that can be tracked simultaneously.
		#[pallet::constant]
		type MaxPublishers: Get<u32>;
		/// Maximum trie depth allowed when processing proofs.
		#[pallet::constant]
		type MaxTrieDepth: Get<u32>;
		/// Maximum size in bytes for cached trie nodes.
		#[pallet::constant]
		type MaxCachedNodeSize: Get<u32>;
	}

	/// Child trie roots from previous block for change detection.
	#[pallet::storage]
	pub type PreviousPublishedDataRoots<T: Config> = StorageValue<
		_,
		BoundedBTreeMap<ParaId, BoundedVec<u8, ConstU32<32>>, T::MaxPublishers>,
		ValueQuery,
	>;

	/// Publishers that have been disabled due to errors (e.g., trie depth exceeded).
	#[pallet::storage]
	pub type DisabledPublishers<T: Config> =
		StorageMap<_, Blake2_128Concat, ParaId, DisableReason, OptionQuery>;

	/// Cached trie nodes for efficient proof verification.
	/// Keyed by (ParaId, node_hash) -> node_data.
	#[pallet::storage]
	pub type CachedTrieNodes<T: Config> = StorageDoubleMap<
		_,
		Blake2_128Concat,
		ParaId,
		Blake2_128Concat,
		H256,
		BoundedVec<u8, T::MaxCachedNodeSize>,
		OptionQuery,
	>;

	/// Cursor for resuming proof processing across blocks.
	/// Stores (ParaId, SubscribedKey) to resume from.
	#[pallet::storage]
	pub type RelayProofProcessingCursor<T: Config> =
		StorageValue<_, (ParaId, SubscribedKey), OptionQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Data was received and processed from a publisher.
		DataProcessed { publisher: ParaId, key: SubscribedKey, value_size: u32 },
		/// A stored publisher root was cleared.
		PublisherRootCleared { publisher: ParaId },
		/// A publisher was disabled due to an error.
		PublisherDisabled { publisher: ParaId, reason: DisableReason },
		/// A previously disabled publisher was re-enabled.
		PublisherEnabled { publisher: ParaId },
		/// Cached trie nodes were cleared for a publisher.
		PublisherCacheCleared { publisher: ParaId },
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Publisher root not found.
		PublisherRootNotFound,
		/// Publisher is not disabled.
		PublisherNotDisabled,
		/// Publisher has no cached nodes.
		NoCachedNodes,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Clear the stored root for a specific publisher.
		///
		/// This forces reprocessing of data from that publisher in the next block.
		/// Useful for recovery scenarios or when a specific publisher's data needs to be refreshed.
		///
		/// - `origin`: Must be root.
		/// - `publisher`: The ParaId of the publisher whose root should be cleared.
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::clear_stored_roots())]
		pub fn clear_stored_roots(origin: OriginFor<T>, publisher: ParaId) -> DispatchResult {
			ensure_root(origin)?;

			<PreviousPublishedDataRoots<T>>::try_mutate(|roots| -> DispatchResult {
				roots.remove(&publisher).ok_or(Error::<T>::PublisherRootNotFound)?;
				Ok(())
			})?;

			Self::deposit_event(Event::PublisherRootCleared { publisher });
			Ok(())
		}

		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::clear_stored_roots())]
		pub fn enable_publisher(origin: OriginFor<T>, publisher: ParaId) -> DispatchResult {
			ensure_root(origin)?;

			<DisabledPublishers<T>>::take(&publisher).ok_or(Error::<T>::PublisherNotDisabled)?;

			Self::deposit_event(Event::PublisherEnabled { publisher });
			Ok(())
		}

		#[pallet::call_index(2)]
		#[pallet::weight(T::WeightInfo::clear_stored_roots())]
		pub fn clear_publisher_cache(origin: OriginFor<T>, publisher: ParaId) -> DispatchResult {
			ensure_root(origin)?;

			let removed = <CachedTrieNodes<T>>::clear_prefix(publisher, u32::MAX, None);
			ensure!(
				removed.maybe_cursor.is_none() || removed.unique > 0,
				Error::<T>::NoCachedNodes
			);

			Self::deposit_event(Event::PublisherCacheCleared { publisher });
			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {
		/// Build relay proof requests from subscriptions.
		/// Excludes disabled publishers from the request.
		pub fn get_relay_proof_requests() -> cumulus_primitives_core::RelayProofRequest {
			let (subscriptions, _weight) = T::SubscriptionHandler::subscriptions();
			let storage_keys = subscriptions
				.into_iter()
				.filter(|(para_id, _)| !<DisabledPublishers<T>>::contains_key(para_id))
				.flat_map(|(para_id, data_keys)| {
					let storage_key = Self::derive_storage_key(para_id);
					data_keys.into_iter().map(move |key| {
						cumulus_primitives_core::RelayStorageKey::Child {
							storage_key: storage_key.clone(),
							key: key.as_ref().to_vec(),
						}
					})
				})
				.collect();

			cumulus_primitives_core::RelayProofRequest { keys: storage_keys }
		}

		/// Derives the child trie storage key for a publisher.
		///
		/// Uses the same encoding pattern as the broadcaster pallet:
		/// `(b"pubsub", para_id).encode()` to ensure compatibility.
		fn derive_storage_key(publisher_para_id: ParaId) -> Vec<u8> {
			use codec::Encode;
			(b"pubsub", publisher_para_id).encode()
		}

		fn derive_child_info(publisher_para_id: ParaId) -> sp_core::storage::ChildInfo {
			sp_core::storage::ChildInfo::new_default(&Self::derive_storage_key(publisher_para_id))
		}

		pub fn collect_publisher_roots(
			relay_state_proof: &RelayChainStateProof,
			subscriptions: &[(ParaId, Vec<SubscribedKey>)],
		) -> BTreeMap<ParaId, Vec<u8>> {
			subscriptions
				.iter()
				.take(T::MaxPublishers::get() as usize)
				.filter(|(publisher_para_id, _)| {
					!<DisabledPublishers<T>>::contains_key(publisher_para_id)
				})
				.filter_map(|(publisher_para_id, _keys)| {
					let child_info = Self::derive_child_info(*publisher_para_id);
					let prefixed_key = child_info.prefixed_storage_key();

					relay_state_proof
						.read_optional_entry::<[u8; 32]>(&prefixed_key)
						.ok()
						.flatten()
						.map(|root_hash| (*publisher_para_id, root_hash.to_vec()))
				})
				.collect()
		}

		pub fn process_published_data(
			relay_state_proof: &RelayChainStateProof,
			current_roots: &BTreeMap<ParaId, Vec<u8>>,
			subscriptions: &[(ParaId, Vec<SubscribedKey>)],
		) -> (Weight, u32) {
			let previous_roots = <PreviousPublishedDataRoots<T>>::get();

			if current_roots.is_empty() && previous_roots.is_empty() {
				return (T::DbWeight::get().reads(1), 0);
			}

			let mut total_handler_weight = Weight::zero();
			let mut total_bytes_decoded = 0u32;

			for (publisher, subscription_keys) in subscriptions {
				if <DisabledPublishers<T>>::contains_key(publisher) {
					continue;
				}

				if let Some(current_root) = current_roots.get(publisher) {
					let should_update = previous_roots
						.get(publisher)
						.map_or(true, |prev_root| prev_root.as_slice() != current_root.as_slice());

					if should_update {
						let child_info = Self::derive_child_info(*publisher);

						for key in subscription_keys.iter() {
							match relay_state_proof.read_child_storage(&child_info, key.as_ref()) {
								Ok(Some(encoded_value)) => {
									let encoded_size = encoded_value.len() as u32;
									total_bytes_decoded =
										total_bytes_decoded.saturating_add(encoded_size);

									match PublishedEntry::<BlockNumberFor<T>>::decode(
										&mut &encoded_value[..],
									) {
										Ok(entry) => {
											let value_size = entry.value.len() as u32;

											let current_block =
												frame_system::Pallet::<T>::block_number();
											let ttl_state = compute_ttl_state(
												entry.ttl,
												entry.when_inserted.saturated_into::<u64>(),
												current_block.saturated_into::<u64>(),
											);

											let handler_weight =
												T::SubscriptionHandler::on_data_updated(
													*publisher,
													*key,
													entry.value.clone(),
													ttl_state,
												);
											total_handler_weight =
												total_handler_weight.saturating_add(handler_weight);

											Self::deposit_event(Event::DataProcessed {
												publisher: *publisher,
												key: *key,
												value_size,
											});
										},
										Err(_) => {
											defensive!("Failed to decode published data value");
										},
									}
								},
								Ok(None) => {},
								Err(_) => {
									defensive!(
										"Failed to read child storage from relay chain proof"
									);
								},
							}
						}
					}
				}
			}

			let bounded_roots: BoundedBTreeMap<
				ParaId,
				BoundedVec<u8, ConstU32<32>>,
				T::MaxPublishers,
			> = current_roots
				.iter()
				.filter_map(|(para_id, root)| {
					BoundedVec::try_from(root.clone())
						.ok()
						.map(|bounded_root| (*para_id, bounded_root))
				})
				.collect::<BTreeMap<_, _>>()
				.try_into()
				.expect("MaxPublishers limit enforced in collect_publisher_roots; qed");
			<PreviousPublishedDataRoots<T>>::put(bounded_roots);

			(total_handler_weight, total_bytes_decoded)
		}

		pub fn disable_publisher(publisher: ParaId, reason: DisableReason) {
			<DisabledPublishers<T>>::insert(publisher, reason);
			Self::deposit_event(Event::PublisherDisabled { publisher, reason });
		}
	}

	impl<T: Config> OnSystemEvent for Pallet<T> {
		fn on_validation_data(_data: &cumulus_primitives_core::PersistedValidationData) {}

		fn on_validation_code_applied() {}

		fn on_relay_state_proof(relay_state_proof: &RelayChainStateProof) -> Weight {
			let (subscriptions, subscriptions_weight) = T::SubscriptionHandler::subscriptions();
			let subscriptions: Vec<(ParaId, Vec<SubscribedKey>)> = subscriptions
				.into_iter()
				.filter(|(para_id, _)| !<DisabledPublishers<T>>::contains_key(para_id))
				.collect();

			let num_publishers = subscriptions.len() as u32;
			let total_keys = subscriptions.iter().map(|(_, keys)| keys.len() as u32).sum();

			let current_roots = Self::collect_publisher_roots(relay_state_proof, &subscriptions);
			let (handler_weight, total_bytes_decoded) =
				Self::process_published_data(relay_state_proof, &current_roots, &subscriptions);

			subscriptions_weight.saturating_add(handler_weight).saturating_add(
				T::WeightInfo::process_proof_excluding_handler(
					num_publishers,
					total_keys,
					total_bytes_decoded,
				),
			)
		}
	}

	impl<T: Config> cumulus_pallet_parachain_system::RelayProofExtender for Pallet<T> {
		fn relay_keys() -> cumulus_primitives_core::RelayProofRequest {
			Self::get_relay_proof_requests()
		}

		fn process_proof(
			db: &sp_trie::MemoryDB<sp_runtime::traits::BlakeTwo256>,
			relay_root: sp_core::H256,
			tracker: &mut sp_trie::accessed_nodes_tracker::AccessedNodesTracker<sp_core::H256>,
			meter: &mut sp_weights::WeightMeter,
			mode: cumulus_pallet_parachain_system::ProcessingMode,
		) -> cumulus_pallet_parachain_system::ProofProcessingResult {
			Self::process_relay_proof(db, relay_root, tracker, meter, mode)
		}
	}

	impl<T: Config> Pallet<T> {
		pub fn process_relay_proof(
			db: &sp_trie::MemoryDB<sp_runtime::traits::BlakeTwo256>,
			relay_root: sp_core::H256,
			tracker: &mut sp_trie::accessed_nodes_tracker::AccessedNodesTracker<sp_core::H256>,
			meter: &mut sp_weights::WeightMeter,
			mode: cumulus_pallet_parachain_system::ProcessingMode,
		) -> cumulus_pallet_parachain_system::ProofProcessingResult {
			use cumulus_pallet_parachain_system::{ProcessingMode, ProofProcessingResult};
			use sp_runtime::traits::BlakeTwo256;
			use sp_trie::{LayoutV1, TrieDBBuilder};
			use trie_db::Trie;

			let cursor = <RelayProofProcessingCursor<T>>::take();
			let (subscriptions, _) = T::SubscriptionHandler::subscriptions();

			let combined: BTreeMap<ParaId, Vec<SubscribedKey>> = subscriptions
				.into_iter()
				.filter(|(para_id, _)| !<DisabledPublishers<T>>::contains_key(para_id))
				.fold(BTreeMap::new(), |mut acc, (para_id, keys)| {
					acc.entry(para_id).or_default().extend(keys);
					acc
				});

			if combined.is_empty() {
				return ProofProcessingResult::Complete;
			}

			let mut work_items: Vec<(ParaId, SubscribedKey)> = combined
				.iter()
				.flat_map(|(para_id, keys)| keys.iter().map(move |key| (*para_id, *key)))
				.collect();

			work_items.sort_by(|(a, _), (b, _)| {
				let a_is_system = u32::from(*a) < 2000;
				let b_is_system = u32::from(*b) < 2000;
				match (a_is_system, b_is_system) {
					(true, false) => core::cmp::Ordering::Less,
					(false, true) => core::cmp::Ordering::Greater,
					_ => u32::from(*a).cmp(&u32::from(*b)),
				}
			});

			let start_idx = cursor
				.and_then(|(cursor_pub, cursor_key)| {
					work_items
						.iter()
						.position(|(pub_id, key)| *pub_id == cursor_pub && *key == cursor_key)
				})
				.unwrap_or(0);

			if start_idx > 0 {
				work_items.rotate_left(start_idx);
			}

			let mut publisher_roots: BTreeMap<ParaId, Option<H256>> = BTreeMap::new();
			let previous_roots = <PreviousPublishedDataRoots<T>>::get();
			let min_op_weight = T::DbWeight::get()
				.reads(1)
				.saturating_add(Weight::from_parts(0, T::MaxCachedNodeSize::get() as u64));

			for (publisher_id, key) in work_items.iter() {
				if !meter.can_consume(min_op_weight) {
					<RelayProofProcessingCursor<T>>::put((*publisher_id, *key));
					return ProofProcessingResult::Incomplete;
				}

				let new_child_root = match publisher_roots.get(publisher_id) {
					Some(Some(root)) => *root,
					Some(None) => continue,
					None => {
						let child_info = Self::derive_child_info(*publisher_id);
						let prefixed_key = child_info.prefixed_storage_key();

						let trie = TrieDBBuilder::<LayoutV1<BlakeTwo256>>::new(db, &relay_root)
							.with_recorder(tracker)
							.build();

						match trie.get(prefixed_key.as_slice()) {
							Ok(Some(root_bytes)) if root_bytes.len() == 32 => {
								let weight = T::DbWeight::get()
									.reads(1)
									.saturating_add(Weight::from_parts(0, root_bytes.len() as u64));
								if !meter.can_consume(weight) {
									<RelayProofProcessingCursor<T>>::put((*publisher_id, *key));
									return ProofProcessingResult::Incomplete;
								}
								meter.consume(weight);

								let mut root_arr = [0u8; 32];
								root_arr.copy_from_slice(&root_bytes);
								let new_root = H256::from(root_arr);

								let old_root = previous_roots
									.get(publisher_id)
									.map(|v| {
										let mut arr = [0u8; 32];
										arr.copy_from_slice(v.as_slice());
										H256::from(arr)
									})
									.unwrap_or_default();

								if new_root == old_root {
									publisher_roots.insert(*publisher_id, None);
									continue;
								}

								publisher_roots.insert(*publisher_id, Some(new_root));
								new_root
							},
							_ => {
								publisher_roots.insert(*publisher_id, None);
								continue;
							},
						}
					},
				};

				match Self::process_key_with_budget(
					db,
					tracker,
					meter,
					*publisher_id,
					new_child_root,
					key,
					mode,
				) {
					Ok(()) => {},
					Err(ProcessKeyError::BudgetExhausted) => {
						<RelayProofProcessingCursor<T>>::put((*publisher_id, *key));
						return ProofProcessingResult::Incomplete;
					},
					Err(ProcessKeyError::TrieDepthExceeded) => {
						if matches!(mode, ProcessingMode::Verify) {
							Self::disable_publisher(
								*publisher_id,
								DisableReason::TrieDepthExceeded,
							);
						}
						publisher_roots.insert(*publisher_id, None);
					},
				}
			}

			if matches!(mode, ProcessingMode::Verify) {
				let bounded_roots: BoundedBTreeMap<
					ParaId,
					BoundedVec<u8, ConstU32<32>>,
					T::MaxPublishers,
				> = publisher_roots
					.iter()
					.filter_map(|(para_id, root)| {
						root.map(|r| {
							let bounded = BoundedVec::try_from(r.as_bytes().to_vec())
								.expect("H256 is always 32 bytes; qed");
							(*para_id, bounded)
						})
					})
					.collect::<BTreeMap<_, _>>()
					.try_into()
					.unwrap_or_default();
				<PreviousPublishedDataRoots<T>>::put(bounded_roots);
			}

			ProofProcessingResult::Complete
		}

		fn process_key_with_budget(
			db: &sp_trie::MemoryDB<sp_runtime::traits::BlakeTwo256>,
			tracker: &mut sp_trie::accessed_nodes_tracker::AccessedNodesTracker<sp_core::H256>,
			meter: &mut sp_weights::WeightMeter,
			publisher_id: ParaId,
			child_root: H256,
			key: &SubscribedKey,
			mode: cumulus_pallet_parachain_system::ProcessingMode,
		) -> Result<(), ProcessKeyError> {
			use cumulus_pallet_parachain_system::ProcessingMode;
			use sp_runtime::traits::BlakeTwo256;
			use sp_trie::{LayoutV1, TrieDBBuilder};
			use trie_db::Trie;

			let min_op_weight = T::DbWeight::get()
				.reads(1)
				.saturating_add(Weight::from_parts(0, T::MaxCachedNodeSize::get() as u64));

			if !meter.can_consume(min_op_weight) {
				return Err(ProcessKeyError::BudgetExhausted);
			}

			let should_cache = matches!(mode, ProcessingMode::Verify);
			let mut composite_recorder = CompositeRecorder::<T>::new(tracker, publisher_id);

			let result = {
				let composite_db = CompositeHashDB::<T>::new(publisher_id, db);
				let trie = TrieDBBuilder::<LayoutV1<BlakeTwo256>>::new(&composite_db, &child_root)
					.with_recorder(&mut composite_recorder)
					.build();

				match trie.get(key.as_ref()) {
					Ok(Some(encoded_value)) => {
						let weight = T::DbWeight::get()
							.reads(1)
							.saturating_add(Weight::from_parts(0, encoded_value.len() as u64));
						meter.consume(weight);

						if should_cache {
							if let Ok(entry) =
								PublishedEntry::<BlockNumberFor<T>>::decode(&mut &encoded_value[..])
							{
								let current_block = frame_system::Pallet::<T>::block_number();
								let ttl_state = compute_ttl_state(
									entry.ttl,
									entry.when_inserted.saturated_into::<u64>(),
									current_block.saturated_into::<u64>(),
								);
								T::SubscriptionHandler::on_data_updated(
									publisher_id,
									*key,
									entry.value.clone(),
									ttl_state,
								);

								Self::deposit_event(Event::DataProcessed {
									publisher: publisher_id,
									key: *key,
									value_size: entry.value.len() as u32,
								});
							}
						}
						Ok(())
					},
					Ok(None) => Ok(()),
					Err(_) => Err(ProcessKeyError::BudgetExhausted),
				}
			};

			// Check depth limit
			if composite_recorder.max_depth() > T::MaxTrieDepth::get() {
				return Err(ProcessKeyError::TrieDepthExceeded);
			}

			if should_cache && result.is_ok() {
				let cached_hashes: Vec<H256> =
					CachedTrieNodes::<T>::iter_prefix(publisher_id).map(|(hash, _)| hash).collect();

				for hash in cached_hashes {
					if !composite_recorder.accessed_hashes().contains(&hash) {
						CachedTrieNodes::<T>::remove(publisher_id, hash);
					}
				}

				composite_recorder.flush_to_cache();
			}

			result
		}
	}
}

#[allow(dead_code)]
enum ProcessKeyError {
	BudgetExhausted,
	TrieDepthExceeded,
}

use core::marker::PhantomData;
use hash_db::{HashDBRef, Hasher, Prefix};
use sp_runtime::traits::BlakeTwo256;

/// A HashDB implementation that reads from `CachedTrieNodes` storage.
///
/// Used to provide cached trie nodes during proof verification, reducing
/// the amount of data that needs to be included in relay proofs.
pub struct CachedTrieNodesDB<T: Config> {
	publisher_id: ParaId,
	_phantom: PhantomData<T>,
}

impl<T: Config> CachedTrieNodesDB<T> {
	pub fn new(publisher_id: ParaId) -> Self {
		Self { publisher_id, _phantom: PhantomData }
	}
}

impl<T: Config> HashDBRef<BlakeTwo256, trie_db::DBValue> for CachedTrieNodesDB<T> {
	fn get(&self, key: &<BlakeTwo256 as Hasher>::Out, _prefix: Prefix) -> Option<trie_db::DBValue> {
		let hash = H256::from_slice(key.as_ref());
		CachedTrieNodes::<T>::get(self.publisher_id, hash).map(|v| v.into_inner())
	}

	fn contains(&self, key: &<BlakeTwo256 as Hasher>::Out, _prefix: Prefix) -> bool {
		let hash = H256::from_slice(key.as_ref());
		CachedTrieNodes::<T>::contains_key(self.publisher_id, hash)
	}
}

/// A composite HashDB that checks cache first, then falls back to proof.
pub struct CompositeHashDB<'a, T: Config> {
	cache_db: CachedTrieNodesDB<T>,
	proof_db: &'a sp_trie::MemoryDB<sp_runtime::traits::BlakeTwo256>,
}

impl<'a, T: Config> CompositeHashDB<'a, T> {
	/// Create a new composite database for a publisher.
	///
	/// The composite DB checks the cache first for each node lookup,
	/// falling back to the proof DB if not cached.
	pub fn new(
		publisher_id: ParaId,
		proof_db: &'a sp_trie::MemoryDB<sp_runtime::traits::BlakeTwo256>,
	) -> Self {
		Self { cache_db: CachedTrieNodesDB::new(publisher_id), proof_db }
	}
}

impl<T: Config> HashDBRef<BlakeTwo256, trie_db::DBValue> for CompositeHashDB<'_, T> {
	fn get(&self, key: &<BlakeTwo256 as Hasher>::Out, prefix: Prefix) -> Option<trie_db::DBValue> {
		// Try cache first
		if let Some(data) = self.cache_db.get(key, prefix) {
			return Some(data);
		}
		// Fall back to proof
		self.proof_db.get(key, prefix)
	}

	fn contains(&self, key: &<BlakeTwo256 as Hasher>::Out, prefix: Prefix) -> bool {
		self.cache_db.contains(key, prefix) || self.proof_db.contains(key, prefix)
	}
}

/// Composite recorder that forwards to AccessedNodesTracker and captures nodes for caching.
pub struct CompositeRecorder<'a, T: Config> {
	tracker: &'a mut sp_trie::accessed_nodes_tracker::AccessedNodesTracker<H256>,
	publisher_id: ParaId,
	accessed_nodes: alloc::vec::Vec<(H256, alloc::vec::Vec<u8>)>,
	accessed_hashes: alloc::collections::BTreeSet<H256>,
	max_node_size: u32,
	current_depth: u32,
	max_depth_reached: u32,
	_phantom: PhantomData<T>,
}

impl<'a, T: Config> CompositeRecorder<'a, T> {
	pub fn new(
		tracker: &'a mut sp_trie::accessed_nodes_tracker::AccessedNodesTracker<H256>,
		publisher_id: ParaId,
	) -> Self {
		Self {
			tracker,
			publisher_id,
			accessed_nodes: alloc::vec::Vec::new(),
			accessed_hashes: alloc::collections::BTreeSet::new(),
			max_node_size: T::MaxCachedNodeSize::get(),
			current_depth: 0,
			max_depth_reached: 0,
			_phantom: PhantomData,
		}
	}

	pub fn max_depth(&self) -> u32 {
		self.max_depth_reached
	}

	pub fn accessed_hashes(&self) -> &alloc::collections::BTreeSet<H256> {
		&self.accessed_hashes
	}

	/// Write all accessed nodes to the cache (Verify mode only).
	pub fn flush_to_cache(self) {
		for (hash, data) in self.accessed_nodes {
			if let Ok(bounded) = BoundedVec::try_from(data) {
				CachedTrieNodes::<T>::insert(self.publisher_id, hash, bounded);
			}
		}
	}
}

impl<T: Config> trie_db::TrieRecorder<H256> for CompositeRecorder<'_, T> {
	fn record(&mut self, access: trie_db::TrieAccess<H256>) {
		match &access {
			trie_db::TrieAccess::EncodedNode { hash, encoded_node, .. } => {
				self.accessed_hashes.insert(*hash);
				self.current_depth = self.current_depth.saturating_add(1);
				self.max_depth_reached = self.max_depth_reached.max(self.current_depth);
				if encoded_node.len() <= self.max_node_size as usize {
					self.accessed_nodes.push((*hash, encoded_node.to_vec()));
				}
			},
			trie_db::TrieAccess::Value { hash, value, .. } => {
				self.accessed_hashes.insert(*hash);
				if value.len() <= self.max_node_size as usize {
					self.accessed_nodes.push((*hash, value.to_vec()));
				}
			},
			_ => {},
		}
		self.tracker.record(access);
	}

	fn trie_nodes_recorded_for_key(&self, key: &[u8]) -> trie_db::RecordedForKey {
		self.tracker.trie_nodes_recorded_for_key(key)
	}
}
