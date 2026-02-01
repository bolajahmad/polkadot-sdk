// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::{mock::*, test_util::build_sproof_with_child_data};
use codec::Encode;
use cumulus_pallet_parachain_system::OnSystemEvent;
use cumulus_primitives_core::ParaId;
use frame_support::{assert_noop, assert_ok};
use polkadot_runtime_parachains::broadcaster::PublishedEntry;

fn key_from_bytes(bytes: &[u8]) -> SubscribedKey {
	SubscribedKey::from_hash({
		let mut arr = [0u8; 32];
		let len = bytes.len().min(32);
		arr[..len].copy_from_slice(&bytes[..len]);
		arr
	})
}

fn encode_published_entry(value: Vec<u8>, ttl: u32, when_inserted: u64) -> Vec<u8> {
	let entry = PublishedEntry { value, ttl, when_inserted };
	entry.encode()
}

fn build_test_proof(
	publisher_para_id: ParaId,
	child_data: Vec<(Vec<u8>, Vec<u8>)>,
) -> cumulus_pallet_parachain_system::RelayChainStateProof {
	build_sproof_with_child_data(&[(publisher_para_id, child_data)])
}

#[test]
fn process_relay_proof_keys_with_new_data_calls_handler() {
	new_test_ext().execute_with(|| {
		ReceivedData::set(vec![]);
		let publisher = ParaId::from(1000);
		let key_bytes = vec![0x12, 0x34];
		let key = key_from_bytes(&key_bytes);
		let value_data = vec![0xAA, 0xBB];
		let value = encode_published_entry(value_data.clone(), 0, 0);

		TestSubscriptions::set(vec![(publisher, vec![key])]);

		let proof = build_test_proof(publisher, vec![(key.as_ref().to_vec(), value.clone())]);

		Pallet::<Test>::on_relay_state_proof(&proof);

		let received = ReceivedData::get();
		assert_eq!(received.len(), 1);
		assert_eq!(received[0].0, publisher);
		assert_eq!(received[0].1, key);
		assert_eq!(received[0].2, value_data);
	});
}

#[test]
fn process_empty_subscriptions() {
	new_test_ext().execute_with(|| {
		ReceivedData::set(vec![]);
		TestSubscriptions::set(vec![]);

		let proof = build_test_proof(ParaId::from(1000), vec![]);

		Pallet::<Test>::on_relay_state_proof(&proof);

		assert_eq!(ReceivedData::get().len(), 0);
	});
}

#[test]
fn root_change_triggers_processing() {
	new_test_ext().execute_with(|| {
		ReceivedData::set(vec![]);
		let publisher = ParaId::from(1000);
		let key_bytes = vec![0x01];
		let key = key_from_bytes(&key_bytes);
		let value1 = encode_published_entry(vec![0x11], 0, 0);
		let value2 = encode_published_entry(vec![0x22], 0, 0);

		TestSubscriptions::set(vec![(publisher, vec![key])]);

		let proof1 = build_test_proof(publisher, vec![(key.as_ref().to_vec(), value1.clone())]);
		Pallet::<Test>::on_relay_state_proof(&proof1);
		assert_eq!(ReceivedData::get().len(), 1);

		ReceivedData::set(vec![]);
		let proof2 = build_test_proof(publisher, vec![(key.as_ref().to_vec(), value2.clone())]);
		Pallet::<Test>::on_relay_state_proof(&proof2);

		assert_eq!(ReceivedData::get().len(), 1);
		assert_eq!(ReceivedData::get()[0].2, vec![0x22]);
	});
}

#[test]
fn unchanged_root_skips_processing() {
	new_test_ext().execute_with(|| {
		ReceivedData::set(vec![]);
		let publisher = ParaId::from(1000);
		let key_bytes = vec![0x01];
		let key = key_from_bytes(&key_bytes);
		let value = encode_published_entry(vec![0x11], 0, 0);

		TestSubscriptions::set(vec![(publisher, vec![key])]);

		let proof = build_test_proof(publisher, vec![(key.as_ref().to_vec(), value.clone())]);
		Pallet::<Test>::on_relay_state_proof(&proof);
		assert_eq!(ReceivedData::get().len(), 1);

		ReceivedData::set(vec![]);
		let proof2 = build_test_proof(publisher, vec![(key.as_ref().to_vec(), value)]);
		Pallet::<Test>::on_relay_state_proof(&proof2);

		assert_eq!(ReceivedData::get().len(), 0, "Handler should not be called for unchanged root");
	});
}

#[test]
fn clear_stored_roots_extrinsic() {
	new_test_ext().execute_with(|| {
		let publisher = ParaId::from(1000);
		let key = key_from_bytes(&[0x01]);
		TestSubscriptions::set(vec![(publisher, vec![key])]);

		let proof = build_test_proof(
			publisher,
			vec![(key.as_ref().to_vec(), encode_published_entry(vec![0x11], 0, 0))],
		);
		Pallet::<Test>::on_relay_state_proof(&proof);

		assert!(PreviousPublishedDataRoots::<Test>::get().contains_key(&publisher));

		assert_ok!(Pallet::<Test>::clear_stored_roots(
			frame_system::RawOrigin::Root.into(),
			publisher
		));

		assert!(!PreviousPublishedDataRoots::<Test>::get().contains_key(&publisher));
	});
}

#[test]
fn clear_stored_roots_only_clears_specified_publisher() {
	new_test_ext().execute_with(|| {
		let publisher1 = ParaId::from(1000);
		let publisher2 = ParaId::from(2000);

		let mut roots = BoundedBTreeMap::new();
		roots
			.try_insert(publisher1, BoundedVec::try_from(vec![0u8; 32]).unwrap())
			.unwrap();
		roots
			.try_insert(publisher2, BoundedVec::try_from(vec![1u8; 32]).unwrap())
			.unwrap();
		PreviousPublishedDataRoots::<Test>::put(roots);

		assert_eq!(PreviousPublishedDataRoots::<Test>::get().len(), 2);

		assert_ok!(Pallet::<Test>::clear_stored_roots(
			frame_system::RawOrigin::Root.into(),
			publisher1
		));

		let roots = PreviousPublishedDataRoots::<Test>::get();
		assert_eq!(roots.len(), 1);
		assert!(!roots.contains_key(&publisher1));
		assert!(roots.contains_key(&publisher2));
	});
}

#[test]
fn clear_stored_roots_fails_if_not_found() {
	new_test_ext().execute_with(|| {
		let publisher = ParaId::from(1000);

		assert_noop!(
			Pallet::<Test>::clear_stored_roots(frame_system::RawOrigin::Root.into(), publisher),
			Error::<Test>::PublisherRootNotFound
		);
	});
}

#[test]
fn data_processed_event_emitted() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);

		let publisher = ParaId::from(1000);
		let key_bytes = vec![0x12];
		let key = key_from_bytes(&key_bytes);
		let value_data = vec![0xAA];
		let value = encode_published_entry(value_data.clone(), 0, 0);

		TestSubscriptions::set(vec![(publisher, vec![key])]);

		let proof = build_test_proof(publisher, vec![(key.as_ref().to_vec(), value.clone())]);
		Pallet::<Test>::on_relay_state_proof(&proof);

		let decoded_len = value_data.len() as u32;

		System::assert_has_event(
			Event::DataProcessed { publisher, key, value_size: decoded_len }.into(),
		);
	});
}

#[test]
fn subscriptions_returns_keys() {
	new_test_ext().execute_with(|| {
		let publisher = ParaId::from(1000);
		let keys = vec![key_from_bytes(&[0x01]), key_from_bytes(&[0x02]), key_from_bytes(&[0x03])];

		TestSubscriptions::set(vec![(publisher, keys.clone())]);

		let (subs, _weight) = <TestHandler as SubscriptionHandler>::subscriptions();
		assert_eq!(subs.len(), 1);
		assert_eq!(subs[0].0, publisher);
		assert_eq!(subs[0].1, keys);
	});
}

#[test]
fn subscriptions_multiple_publishers() {
	new_test_ext().execute_with(|| {
		let publisher1 = ParaId::from(1000);
		let publisher2 = ParaId::from(2000);
		let keys1 = vec![key_from_bytes(&[0x01])];
		let keys2 = vec![key_from_bytes(&[0x02]), key_from_bytes(&[0x03])];

		TestSubscriptions::set(vec![(publisher1, keys1.clone()), (publisher2, keys2.clone())]);

		let (subs, _weight) = <TestHandler as SubscriptionHandler>::subscriptions();
		assert_eq!(subs.len(), 2);

		let sub1 = subs.iter().find(|(p, _)| *p == publisher1).unwrap();
		assert_eq!(sub1.1, keys1);

		let sub2 = subs.iter().find(|(p, _)| *p == publisher2).unwrap();
		assert_eq!(sub2.1, keys2);
	});
}

#[test]
fn subscriptions_empty_returns_empty() {
	new_test_ext().execute_with(|| {
		TestSubscriptions::set(vec![]);

		let (subs, _weight) = <TestHandler as SubscriptionHandler>::subscriptions();
		assert!(subs.is_empty());
	});
}

#[test]
fn relay_keys_includes_subscribed() {
	new_test_ext().execute_with(|| {
		let publisher = ParaId::from(1000);
		let key1 = key_from_bytes(&[0x01]);
		let key2 = key_from_bytes(&[0x02]);

		TestSubscriptions::set(vec![(publisher, vec![key1, key2])]);

		let request = Pallet::<Test>::get_relay_proof_requests();
		assert_eq!(request.keys.len(), 2);

		use cumulus_primitives_core::RelayStorageKey;
		let expected_storage_key = (b"pubsub", publisher).encode();

		for relay_key in &request.keys {
			match relay_key {
				RelayStorageKey::Child { storage_key, key } => {
					assert_eq!(*storage_key, expected_storage_key);
					assert!(key == key1.as_ref() || key == key2.as_ref());
				},
				_ => panic!("Expected Child storage key"),
			}
		}
	});
}

#[test]
fn relay_keys_empty_no_subscriptions() {
	new_test_ext().execute_with(|| {
		TestSubscriptions::set(vec![]);

		let request = Pallet::<Test>::get_relay_proof_requests();
		assert!(request.keys.is_empty());
	});
}

#[test]
fn relay_keys_multiple_publishers() {
	new_test_ext().execute_with(|| {
		let publisher1 = ParaId::from(1000);
		let publisher2 = ParaId::from(2000);
		let key1 = key_from_bytes(&[0x01]);
		let key2 = key_from_bytes(&[0x02]);

		TestSubscriptions::set(vec![(publisher1, vec![key1]), (publisher2, vec![key2])]);

		let request = Pallet::<Test>::get_relay_proof_requests();
		assert_eq!(request.keys.len(), 2);
	});
}

#[test]
fn new_publisher_processed_on_first_appearance() {
	new_test_ext().execute_with(|| {
		ReceivedData::set(vec![]);
		let publisher = ParaId::from(1000);
		let key = key_from_bytes(&[0x01]);
		let value = encode_published_entry(vec![0x11], 0, 0);

		TestSubscriptions::set(vec![(publisher, vec![key])]);

		assert!(!PreviousPublishedDataRoots::<Test>::get().contains_key(&publisher));

		let proof = build_test_proof(publisher, vec![(key.as_ref().to_vec(), value.clone())]);
		Pallet::<Test>::on_relay_state_proof(&proof);

		assert_eq!(ReceivedData::get().len(), 1);
		assert!(PreviousPublishedDataRoots::<Test>::get().contains_key(&publisher));
	});
}

#[test]
fn multiple_publishers_mixed_changes() {
	new_test_ext().execute_with(|| {
		let publisher1 = ParaId::from(1000);
		let publisher2 = ParaId::from(2000);
		let key1 = key_from_bytes(&[0x01]);
		let key2 = key_from_bytes(&[0x02]);
		let value1 = encode_published_entry(vec![0x11], 0, 0);
		let value2 = encode_published_entry(vec![0x22], 0, 0);

		TestSubscriptions::set(vec![(publisher1, vec![key1]), (publisher2, vec![key2])]);

		ReceivedData::set(vec![]);
		let proof = build_sproof_with_child_data(&[
			(publisher1, vec![(key1.as_ref().to_vec(), value1.clone())]),
			(publisher2, vec![(key2.as_ref().to_vec(), value2.clone())]),
		]);
		Pallet::<Test>::on_relay_state_proof(&proof);
		assert_eq!(ReceivedData::get().len(), 2);

		ReceivedData::set(vec![]);
		let new_value1 = encode_published_entry(vec![0x33], 0, 0);
		let proof2 = build_sproof_with_child_data(&[
			(publisher1, vec![(key1.as_ref().to_vec(), new_value1.clone())]),
			(publisher2, vec![(key2.as_ref().to_vec(), value2.clone())]),
		]);
		Pallet::<Test>::on_relay_state_proof(&proof2);

		let received = ReceivedData::get();
		assert_eq!(received.len(), 1);
		assert_eq!(received[0].0, publisher1);
	});
}

#[test]
fn key_not_in_trie_no_callback() {
	new_test_ext().execute_with(|| {
		ReceivedData::set(vec![]);
		let publisher = ParaId::from(1000);
		let subscribed_key = key_from_bytes(&[0x01]);
		let published_key = [0x02u8; 32];
		let value = encode_published_entry(vec![0x11], 0, 0);

		TestSubscriptions::set(vec![(publisher, vec![subscribed_key])]);

		let proof = build_test_proof(publisher, vec![(published_key.to_vec(), value)]);
		Pallet::<Test>::on_relay_state_proof(&proof);

		assert_eq!(ReceivedData::get().len(), 0);
	});
}

#[test]
fn multiple_keys_same_publisher() {
	new_test_ext().execute_with(|| {
		ReceivedData::set(vec![]);
		let publisher = ParaId::from(1000);
		let key1 = key_from_bytes(&[0x01]);
		let key2 = key_from_bytes(&[0x02]);
		let key3 = key_from_bytes(&[0x03]);
		let value1 = encode_published_entry(vec![0x11], 0, 0);
		let value2 = encode_published_entry(vec![0x22], 0, 0);
		let value3 = encode_published_entry(vec![0x33], 0, 0);

		TestSubscriptions::set(vec![(publisher, vec![key1, key2, key3])]);

		let proof = build_test_proof(
			publisher,
			vec![
				(key1.as_ref().to_vec(), value1.clone()),
				(key2.as_ref().to_vec(), value2.clone()),
				(key3.as_ref().to_vec(), value3.clone()),
			],
		);
		Pallet::<Test>::on_relay_state_proof(&proof);

		let received = ReceivedData::get();
		assert_eq!(received.len(), 3);

		let keys_received: Vec<_> = received.iter().map(|(_, k, _, _)| *k).collect();
		assert!(keys_received.contains(&key1));
		assert!(keys_received.contains(&key2));
		assert!(keys_received.contains(&key3));
	});
}

// ============================================================================
// New tests for DisabledPublishers and enable_publisher
// ============================================================================

#[test]
fn disabled_publisher_skipped_in_proof_requests() {
	new_test_ext().execute_with(|| {
		let publisher1 = ParaId::from(1000);
		let publisher2 = ParaId::from(2000);
		let key1 = key_from_bytes(&[0x01]);
		let key2 = key_from_bytes(&[0x02]);

		TestSubscriptions::set(vec![(publisher1, vec![key1]), (publisher2, vec![key2])]);

		DisabledPublishers::<Test>::insert(publisher1, DisableReason::TrieDepthExceeded);

		let request = Pallet::<Test>::get_relay_proof_requests();
		assert_eq!(request.keys.len(), 1);

		use cumulus_primitives_core::RelayStorageKey;
		match &request.keys[0] {
			RelayStorageKey::Child { storage_key, .. } => {
				let expected = (b"pubsub", publisher2).encode();
				assert_eq!(*storage_key, expected);
			},
			_ => panic!("Expected Child storage key"),
		}
	});
}

#[test]
fn disabled_publisher_skipped_in_processing() {
	new_test_ext().execute_with(|| {
		ReceivedData::set(vec![]);
		let publisher = ParaId::from(1000);
		let key = key_from_bytes(&[0x01]);
		let value = encode_published_entry(vec![0x11], 0, 0);

		TestSubscriptions::set(vec![(publisher, vec![key])]);
		DisabledPublishers::<Test>::insert(publisher, DisableReason::TrieDepthExceeded);

		let proof = build_test_proof(publisher, vec![(key.as_ref().to_vec(), value)]);
		Pallet::<Test>::on_relay_state_proof(&proof);

		assert_eq!(ReceivedData::get().len(), 0);
	});
}

#[test]
fn enable_publisher_works() {
	new_test_ext().execute_with(|| {
		let publisher = ParaId::from(1000);

		DisabledPublishers::<Test>::insert(publisher, DisableReason::TrieDepthExceeded);
		assert!(DisabledPublishers::<Test>::contains_key(&publisher));

		assert_ok!(Pallet::<Test>::enable_publisher(
			frame_system::RawOrigin::Root.into(),
			publisher
		));

		assert!(!DisabledPublishers::<Test>::contains_key(&publisher));
	});
}

#[test]
fn enable_publisher_emits_event() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		let publisher = ParaId::from(1000);

		DisabledPublishers::<Test>::insert(publisher, DisableReason::TrieDepthExceeded);

		assert_ok!(Pallet::<Test>::enable_publisher(
			frame_system::RawOrigin::Root.into(),
			publisher
		));

		System::assert_has_event(Event::PublisherEnabled { publisher }.into());
	});
}

#[test]
fn enable_publisher_fails_if_not_disabled() {
	new_test_ext().execute_with(|| {
		let publisher = ParaId::from(1000);

		assert_noop!(
			Pallet::<Test>::enable_publisher(frame_system::RawOrigin::Root.into(), publisher),
			Error::<Test>::PublisherNotDisabled
		);
	});
}

#[test]
fn enable_publisher_requires_root_origin() {
	new_test_ext().execute_with(|| {
		let publisher = ParaId::from(1000);

		DisabledPublishers::<Test>::insert(publisher, DisableReason::TrieDepthExceeded);

		assert_noop!(
			Pallet::<Test>::enable_publisher(
				frame_system::RawOrigin::Signed(1u64).into(),
				publisher
			),
			frame_support::error::BadOrigin
		);

		assert!(DisabledPublishers::<Test>::contains_key(&publisher));
	});
}

#[test]
fn disable_publisher_function_works() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		let publisher = ParaId::from(1000);

		assert!(!DisabledPublishers::<Test>::contains_key(&publisher));

		Pallet::<Test>::disable_publisher(publisher, DisableReason::TrieDepthExceeded);

		assert!(DisabledPublishers::<Test>::contains_key(&publisher));
		assert_eq!(
			DisabledPublishers::<Test>::get(&publisher),
			Some(DisableReason::TrieDepthExceeded)
		);

		System::assert_has_event(
			Event::PublisherDisabled { publisher, reason: DisableReason::TrieDepthExceeded }.into(),
		);
	});
}

#[test]
fn reenabled_publisher_processed_again() {
	new_test_ext().execute_with(|| {
		ReceivedData::set(vec![]);
		let publisher = ParaId::from(1000);
		let key = key_from_bytes(&[0x01]);
		let value = encode_published_entry(vec![0x11], 0, 0);

		TestSubscriptions::set(vec![(publisher, vec![key])]);
		DisabledPublishers::<Test>::insert(publisher, DisableReason::TrieDepthExceeded);

		let proof = build_test_proof(publisher, vec![(key.as_ref().to_vec(), value.clone())]);
		Pallet::<Test>::on_relay_state_proof(&proof);
		assert_eq!(ReceivedData::get().len(), 0);

		assert_ok!(Pallet::<Test>::enable_publisher(
			frame_system::RawOrigin::Root.into(),
			publisher
		));

		let proof2 = build_test_proof(publisher, vec![(key.as_ref().to_vec(), value)]);
		Pallet::<Test>::on_relay_state_proof(&proof2);

		assert_eq!(ReceivedData::get().len(), 1);
	});
}

// ============================================================================
// Tests for TtlState and compute_ttl_state
// ============================================================================

#[test]
fn compute_ttl_state_infinite() {
	assert_eq!(compute_ttl_state(0u32, 100u64, 200u64), TtlState::Infinite);
}

#[test]
fn compute_ttl_state_valid_for() {
	assert_eq!(compute_ttl_state(100u32, 100u64, 150u64), TtlState::ValidFor(50));
}

#[test]
fn compute_ttl_state_timed_out() {
	assert_eq!(compute_ttl_state(100u32, 100u64, 200u64), TtlState::TimedOut);
}

#[test]
fn compute_ttl_state_exactly_at_expiration() {
	assert_eq!(compute_ttl_state(100u32, 100u64, 200u64), TtlState::TimedOut);
}

#[test]
fn compute_ttl_state_one_block_before_expiration() {
	assert_eq!(compute_ttl_state(100u32, 100u64, 199u64), TtlState::ValidFor(1));
}

// TTL State Computation Tests
#[test]
fn ttl_zero_returns_infinite() {
	// TTL=0 means infinite, regardless of block numbers
	let result = compute_ttl_state(0, 1000u64, 5000u64);
	assert_eq!(result, TtlState::Infinite);
}

#[test]
fn ttl_with_remaining_blocks_returns_valid_for() {
	// Inserted at block 1000, TTL=100, current block=1050
	// Expiration is at block 1100, so 50 blocks remaining
	let result = compute_ttl_state(100, 1000u64, 1050u64);
	assert_eq!(result, TtlState::ValidFor(50));
}

#[test]
fn ttl_expired_returns_timed_out() {
	// Inserted at block 1000, TTL=100, current block=1200
	// Expiration was at block 1100, so it's timed out
	let result = compute_ttl_state(100, 1000u64, 1200u64);
	assert_eq!(result, TtlState::TimedOut);
}

#[test]
fn ttl_exactly_at_expiry_returns_timed_out() {
	// Inserted at block 1000, TTL=100, current block=1100
	// Expiration is exactly at 1100, which means timed out (>= check)
	let result = compute_ttl_state(100, 1000u64, 1100u64);
	assert_eq!(result, TtlState::TimedOut);
}

#[test]
fn ttl_one_block_before_expiry_returns_valid_for_one() {
	// Inserted at block 1000, TTL=100, current block=1099
	// Expiration is at 1100, so 1 block remaining
	let result = compute_ttl_state(100, 1000u64, 1099u64);
	assert_eq!(result, TtlState::ValidFor(1));
}

// ============================================================================
// Tests for SubscribedKey
// ============================================================================

#[test]
fn subscribed_key_from_hash() {
	let hash = [0x42u8; 32];
	let key = SubscribedKey::from_hash(hash);
	assert_eq!(key.as_bytes(), &hash);
}

#[test]
fn subscribed_key_from_data() {
	let data = b"test_key";
	let key = SubscribedKey::from_data(data);
	let expected = sp_crypto_hashing::blake2_256(data);
	assert_eq!(key.as_bytes(), &expected);
}

#[test]
fn subscribed_key_macro() {
	let key = subscribed_key!("my_key");
	let expected = sp_crypto_hashing::blake2_256(b"my_key");
	assert_eq!(key.as_bytes(), &expected);
}

mod process_proof_tests {
	use super::*;
	use cumulus_pallet_parachain_system::{ProcessingMode, ProofProcessingResult};
	use frame_support::weights::Weight;
	use sp_core::H256;
	use sp_runtime::traits::BlakeTwo256;
	use sp_trie::{accessed_nodes_tracker::AccessedNodesTracker, MemoryDB};
	use sp_weights::WeightMeter;

	fn build_memory_db_from_proof(
		publishers: &[(ParaId, Vec<(Vec<u8>, Vec<u8>)>)],
	) -> (MemoryDB<BlakeTwo256>, H256) {
		let proof = crate::test_util::build_sproof_with_child_data(publishers);
		let (storage_proof, root) = proof.into_parts();
		let db: MemoryDB<BlakeTwo256> = storage_proof.into_memory_db();
		(db, root)
	}

	#[test]
	fn process_proof_with_sufficient_budget_returns_complete() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);

			let (db, root) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value)])]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert_eq!(result, ProofProcessingResult::Complete);
		});
	}

	#[test]
	fn process_proof_with_zero_budget_returns_incomplete() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);

			let (db, root) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value)])]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::with_limit(Weight::zero());

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert_eq!(result, ProofProcessingResult::Incomplete);
		});
	}

	#[test]
	fn process_proof_stores_cursor_on_incomplete() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);

			let (db, root) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value)])]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::with_limit(Weight::zero());

			let _ = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			let cursor = RelayProofProcessingCursor::<Test>::get();
			assert!(cursor.is_some());
			let (cursor_pub, cursor_key) = cursor.unwrap();
			assert_eq!(cursor_pub, publisher);
			assert_eq!(cursor_key, key);
		});
	}

	#[test]
	fn process_proof_empty_subscriptions_returns_complete() {
		new_test_ext().execute_with(|| {
			TestSubscriptions::set(vec![]);

			let db = MemoryDB::<BlakeTwo256>::default();
			let root = H256::default();
			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert_eq!(result, ProofProcessingResult::Complete);
		});
	}

	#[test]
	fn process_proof_skips_disabled_publishers() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);
			DisabledPublishers::<Test>::insert(publisher, DisableReason::TrieDepthExceeded);

			let (db, root) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value)])]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert_eq!(result, ProofProcessingResult::Complete);
			assert_eq!(ReceivedData::get().len(), 0);
		});
	}

	#[test]
	fn process_proof_prune_mode_does_not_call_handler() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);

			let (db, root) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value)])]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Prune,
			);

			assert_eq!(result, ProofProcessingResult::Complete);
			assert_eq!(ReceivedData::get().len(), 0);
		});
	}

	#[test]
	fn process_proof_with_limited_budget_stops_early() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher1 = ParaId::from(1000);
			let publisher2 = ParaId::from(1001);
			let key1 = key_from_bytes(&[0x01]);
			let key2 = key_from_bytes(&[0x02]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(publisher1, vec![key1]), (publisher2, vec![key2])]);

			let (db, root) = build_memory_db_from_proof(&[
				(publisher1, vec![(key1.as_ref().to_vec(), value.clone())]),
				(publisher2, vec![(key2.as_ref().to_vec(), value)]),
			]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let very_small_budget = Weight::from_parts(1, 1);
			let mut meter = WeightMeter::with_limit(very_small_budget);

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert_eq!(result, ProofProcessingResult::Incomplete);
		});
	}

	#[test]
	fn process_proof_prioritizes_system_chains() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let system_chain = ParaId::from(1000);
			let non_system_chain = ParaId::from(3000);
			let key1 = key_from_bytes(&[0x01]);
			let key2 = key_from_bytes(&[0x02]);
			let value1 = encode_published_entry(vec![0x11], 0, 0);
			let value2 = encode_published_entry(vec![0x22], 0, 0);

			TestSubscriptions::set(vec![
				(non_system_chain, vec![key2]),
				(system_chain, vec![key1]),
			]);

			let (db, root) = build_memory_db_from_proof(&[
				(non_system_chain, vec![(key2.as_ref().to_vec(), value2)]),
				(system_chain, vec![(key1.as_ref().to_vec(), value1)]),
			]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();

			let _ = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			let received = ReceivedData::get();
			if received.len() >= 2 {
				assert!(u32::from(received[0].0) < 2000, "System chain should be processed first");
			}
		});
	}

	#[test]
	fn process_proof_verify_mode_caches_nodes() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);

			let (db, root) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value)])]);

			assert!(!CachedTrieNodes::<Test>::iter_prefix(publisher).next().is_some());

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert_eq!(result, ProofProcessingResult::Complete);
			assert!(CachedTrieNodes::<Test>::iter_prefix(publisher).next().is_some());
		});
	}

	#[test]
	fn process_proof_prune_mode_does_not_cache_nodes() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);

			let (db, root) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value)])]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Prune,
			);

			assert_eq!(result, ProofProcessingResult::Complete);
			assert!(!CachedTrieNodes::<Test>::iter_prefix(publisher).next().is_some());
		});
	}

	#[test]
	fn process_proof_weight_tracking_consumes_proof_size() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11; 100], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);

			let (db, root) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value)])]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();

			let initial_consumed = meter.consumed();

			let _ = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			let consumed = meter.consumed();
			assert!(
				consumed.proof_size() > initial_consumed.proof_size(),
				"Should consume proof_size weight"
			);
		});
	}

	#[test]
	fn process_proof_large_budget_processes_all_keys() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let keys: Vec<_> = (0..10).map(|i| key_from_bytes(&[i])).collect();
			let data: Vec<_> = keys
				.iter()
				.enumerate()
				.map(|(i, k)| {
					(k.as_ref().to_vec(), encode_published_entry(vec![i as u8; 32], 0, 0))
				})
				.collect();

			TestSubscriptions::set(vec![(publisher, keys.clone())]);

			let (db, root) = build_memory_db_from_proof(&[(publisher, data)]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let large_budget = Weight::from_parts(u64::MAX, u64::MAX);
			let mut meter = WeightMeter::with_limit(large_budget);

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert_eq!(result, ProofProcessingResult::Complete);
			assert_eq!(ReceivedData::get().len(), 10);
		});
	}

	#[test]
	fn process_proof_tiny_budget_returns_incomplete_immediately() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);

			let (db, root) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value)])]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let tiny_budget = Weight::from_parts(1, 1);
			let mut meter = WeightMeter::with_limit(tiny_budget);

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert_eq!(result, ProofProcessingResult::Incomplete);
			assert_eq!(ReceivedData::get().len(), 0);
			assert!(RelayProofProcessingCursor::<Test>::get().is_some());
		});
	}

	#[test]
	fn process_proof_zero_budget_graceful_skip() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);

			let (db, root) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value)])]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let zero_budget = Weight::zero();
			let mut meter = WeightMeter::with_limit(zero_budget);

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert_eq!(result, ProofProcessingResult::Incomplete);
			assert_eq!(ReceivedData::get().len(), 0);
		});
	}

	#[test]
	fn process_proof_prune_and_verify_consume_similar_weight() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11; 64], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);

			let (db, root) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value)])]);

			let mut tracker_prune = AccessedNodesTracker::<H256>::new(0);
			let mut meter_prune = WeightMeter::new();

			let _ = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker_prune,
				&mut meter_prune,
				ProcessingMode::Prune,
			);

			let mut tracker_verify = AccessedNodesTracker::<H256>::new(0);
			let mut meter_verify = WeightMeter::new();

			let _ = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker_verify,
				&mut meter_verify,
				ProcessingMode::Verify,
			);

			let prune_consumed = meter_prune.consumed();
			let verify_consumed = meter_verify.consumed();

			assert_eq!(
				prune_consumed.proof_size(),
				verify_consumed.proof_size(),
				"Prune and Verify modes should consume same proof_size"
			);
		});
	}

	#[test]
	fn process_proof_cursor_resumes_from_correct_position() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key1 = key_from_bytes(&[0x01]);
			let key2 = key_from_bytes(&[0x02]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key1, key2])]);

			let (db, root) = build_memory_db_from_proof(&[(
				publisher,
				vec![(key1.as_ref().to_vec(), value.clone()), (key2.as_ref().to_vec(), value)],
			)]);

			RelayProofProcessingCursor::<Test>::put((publisher, key2));

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert_eq!(result, ProofProcessingResult::Complete);
			let received = ReceivedData::get();
			assert!(!received.is_empty());
			assert_eq!(received[0].1, key2, "Should start from cursor position");
		});
	}

	#[test]
	fn process_proof_multiple_publishers_partial_processing() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let pub1 = ParaId::from(1000);
			let pub2 = ParaId::from(2000);
			let key1 = key_from_bytes(&[0x01]);
			let key2 = key_from_bytes(&[0x02]);
			let value = encode_published_entry(vec![0x11; 100], 0, 0);

			TestSubscriptions::set(vec![(pub1, vec![key1]), (pub2, vec![key2])]);

			let (db, root) = build_memory_db_from_proof(&[
				(pub1, vec![(key1.as_ref().to_vec(), value.clone())]),
				(pub2, vec![(key2.as_ref().to_vec(), value)]),
			]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let small_budget = Weight::from_parts(10_000_000, 500);
			let mut meter = WeightMeter::with_limit(small_budget);

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			if result == ProofProcessingResult::Incomplete {
				let cursor = RelayProofProcessingCursor::<Test>::get();
				assert!(cursor.is_some());
			}
		});
	}

	#[test]
	fn process_proof_updates_previous_roots_in_verify_mode() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);

			assert!(PreviousPublishedDataRoots::<Test>::get().get(&publisher).is_none());

			let (db, root) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value)])]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();

			let _ = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert!(PreviousPublishedDataRoots::<Test>::get().get(&publisher).is_some());
		});
	}

	#[test]
	fn process_proof_prune_mode_does_not_update_roots() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);

			let (db, root) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value)])]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();

			let _ = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Prune,
			);

			assert!(PreviousPublishedDataRoots::<Test>::get().get(&publisher).is_none());
		});
	}

	#[test]
	fn cache_invalidation_removes_stale_nodes() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);

			TestSubscriptions::set(vec![(publisher, vec![key])]);
			let value1 = encode_published_entry(vec![0x11], 0, 0);
			let (db1, root1) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value1)])]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();
			Pallet::<Test>::process_relay_proof(
				&db1,
				root1,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			let initial_cache_count: usize =
				CachedTrieNodes::<Test>::iter_prefix(publisher).count();
			assert!(initial_cache_count > 0, "Cache should have entries after first proof");

			let value2 = encode_published_entry(vec![0x22, 0x33, 0x44], 0, 0);
			let (db2, root2) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value2)])]);

			let mut tracker2 = AccessedNodesTracker::<H256>::new(0);
			let mut meter2 = WeightMeter::new();
			Pallet::<Test>::process_relay_proof(
				&db2,
				root2,
				&mut tracker2,
				&mut meter2,
				ProcessingMode::Verify,
			);

			let final_cache_count: usize = CachedTrieNodes::<Test>::iter_prefix(publisher).count();
			assert!(final_cache_count > 0, "Cache should still have entries after second proof");
		});
	}

	#[test]
	fn clear_publisher_cache_removes_all_entries() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);
			let (db, root) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value)])]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();
			Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert!(
				CachedTrieNodes::<Test>::iter_prefix(publisher).count() > 0,
				"Cache should be populated"
			);

			assert_ok!(Subscriber::clear_publisher_cache(
				frame_system::RawOrigin::Root.into(),
				publisher
			));

			assert_eq!(
				CachedTrieNodes::<Test>::iter_prefix(publisher).count(),
				0,
				"Cache should be cleared"
			);
		});
	}

	#[test]
	fn composite_hash_db_checks_cache_first() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);
			let (db, root) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value)])]);

			for _ in 0..2 {
				let mut tracker = AccessedNodesTracker::<H256>::new(0);
				let mut meter = WeightMeter::new();
				let result = Pallet::<Test>::process_relay_proof(
					&db,
					root,
					&mut tracker,
					&mut meter,
					ProcessingMode::Verify,
				);
				assert_eq!(result, ProofProcessingResult::Complete);
			}

			assert!(
				CachedTrieNodes::<Test>::iter_prefix(publisher).count() > 0,
				"Cache should have entries"
			);
		});
	}

	#[test]
	fn system_parachains_processed_first() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let system_para = ParaId::from(1000);
			let non_system_para = ParaId::from(3000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(non_system_para, vec![key]), (system_para, vec![key])]);

			let (db, root) = build_memory_db_from_proof(&[
				(system_para, vec![(key.as_ref().to_vec(), value.clone())]),
				(non_system_para, vec![(key.as_ref().to_vec(), value)]),
			]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert_eq!(result, ProofProcessingResult::Complete);

			let received = ReceivedData::get();
			assert!(received.len() >= 2, "Should have processed at least 2 items");

			if received.len() >= 2 {
				assert_eq!(
					received[0].0, system_para,
					"System parachain (ID < 2000) should be processed first"
				);
				assert_eq!(
					received[1].0, non_system_para,
					"Non-system parachain should be processed second"
				);
			}
		});
	}

	#[test]
	fn all_proof_nodes_accessed_complete_processing() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);

			let (db, root) =
				build_memory_db_from_proof(&[(publisher, vec![(key.as_ref().to_vec(), value)])]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert_eq!(result, ProofProcessingResult::Complete);
			assert!(
				meter.consumed().proof_size() > 0,
				"Proof nodes should have been accessed (proof_size consumed)"
			);
		});
	}

	#[test]
	fn incomplete_at_budget_limit_sets_cursor() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key1 = key_from_bytes(&[0x01]);
			let key2 = key_from_bytes(&[0x02]);
			let value = encode_published_entry(vec![0x11; 100], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key1, key2])]);

			let (db, root) = build_memory_db_from_proof(&[(
				publisher,
				vec![(key1.as_ref().to_vec(), value.clone()), (key2.as_ref().to_vec(), value)],
			)]);

			let tiny_budget = Weight::from_parts(1, 1);
			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::with_limit(tiny_budget);

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert_eq!(
				result,
				ProofProcessingResult::Incomplete,
				"Should return Incomplete when budget exhausted"
			);
			assert!(
				RelayProofProcessingCursor::<Test>::get().is_some(),
				"Cursor should be set for resumption"
			);
		});
	}

	#[test]
	fn value_exactly_32_bytes_inline_storage() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value_32_bytes = encode_published_entry(vec![0xAB; 32], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);

			let (db, root) = build_memory_db_from_proof(&[(
				publisher,
				vec![(key.as_ref().to_vec(), value_32_bytes)],
			)]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert_eq!(result, ProofProcessingResult::Complete);
			let received = ReceivedData::get();
			assert!(!received.is_empty(), "32-byte value should be processed");
		});
	}

	#[test]
	fn value_exactly_33_bytes_external_storage() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);
			let value_33_bytes = encode_published_entry(vec![0xCD; 33], 0, 0);

			TestSubscriptions::set(vec![(publisher, vec![key])]);

			let (db, root) = build_memory_db_from_proof(&[(
				publisher,
				vec![(key.as_ref().to_vec(), value_33_bytes)],
			)]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert_eq!(result, ProofProcessingResult::Complete);
			let received = ReceivedData::get();
			assert!(!received.is_empty(), "33-byte value should be processed");
		});
	}

	#[test]
	fn empty_child_trie_no_data() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let publisher = ParaId::from(1000);
			let key = key_from_bytes(&[0x01]);

			TestSubscriptions::set(vec![(publisher, vec![key])]);

			let (db, root) = build_memory_db_from_proof(&[(publisher, vec![])]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert_eq!(result, ProofProcessingResult::Complete);
			let received = ReceivedData::get();
			assert!(received.is_empty(), "Empty trie should produce no data");
		});
	}

	#[test]
	fn subscription_to_non_existent_publisher() {
		new_test_ext().execute_with(|| {
			ReceivedData::set(vec![]);
			let subscribed_publisher = ParaId::from(1000);
			let actual_publisher = ParaId::from(2000);
			let key = key_from_bytes(&[0x01]);
			let value = encode_published_entry(vec![0x11], 0, 0);

			TestSubscriptions::set(vec![(subscribed_publisher, vec![key])]);

			let (db, root) = build_memory_db_from_proof(&[(
				actual_publisher,
				vec![(key.as_ref().to_vec(), value)],
			)]);

			let mut tracker = AccessedNodesTracker::<H256>::new(0);
			let mut meter = WeightMeter::new();

			let result = Pallet::<Test>::process_relay_proof(
				&db,
				root,
				&mut tracker,
				&mut meter,
				ProcessingMode::Verify,
			);

			assert_eq!(result, ProofProcessingResult::Complete);
			let received = ReceivedData::get();
			assert!(
				received.is_empty(),
				"No data should be received for non-existent publisher subscription"
			);
		});
	}
}
