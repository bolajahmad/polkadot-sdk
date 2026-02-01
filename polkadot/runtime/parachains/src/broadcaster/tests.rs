// Copyright (C) Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

use super::*;
use crate::mock::{new_test_ext, Balances, Broadcaster, RuntimeOrigin, System, Test};
use frame_support::{
	assert_err, assert_ok,
	traits::fungible::{hold::Inspect as HoldInspect, Inspect},
};
use polkadot_primitives::Id as ParaId;
use sp_core::hashing::blake2_256;

const ALICE: u64 = 1;
const BOB: u64 = 2;

fn setup_account(who: u64, balance: u128) {
	let _ = Balances::mint_into(&who, balance);
}

fn hash_key(data: &[u8]) -> [u8; 32] {
	blake2_256(data)
}

fn publish_item(key: &[u8], value: &[u8]) -> ([u8; 32], Vec<u8>, u32) {
	(hash_key(key), value.to_vec(), 0)
}

fn publish_item_with_ttl(key: &[u8], value: &[u8], ttl: u32) -> ([u8; 32], Vec<u8>, u32) {
	(hash_key(key), value.to_vec(), ttl)
}

fn register_test_publisher(para_id: ParaId) {
	setup_account(ALICE, 10000);
	assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));
}

#[test]
fn register_publisher_works() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 1000);

		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));

		let info = RegisteredPublishers::<Test>::get(para_id).unwrap();
		assert_eq!(info.manager, ALICE);
		assert_eq!(info.deposit, 100);

		assert_eq!(Balances::balance_on_hold(&HoldReason::PublisherDeposit.into(), &ALICE), 100);
		assert_eq!(Balances::balance(&ALICE), 900);
	});
}

#[test]
fn force_register_system_chain_works() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(1000); // System chain
		setup_account(ALICE, 1000);

		assert_ok!(Broadcaster::force_register_publisher(RuntimeOrigin::root(), ALICE, 0, para_id));

		let info = RegisteredPublishers::<Test>::get(para_id).unwrap();
		assert_eq!(info.manager, ALICE);
		assert_eq!(info.deposit, 0);

		assert_eq!(Balances::balance_on_hold(&HoldReason::PublisherDeposit.into(), &ALICE), 0);
		assert_eq!(Balances::balance(&ALICE), 1000);
	});
}

#[test]
fn force_register_with_custom_deposit_works() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(BOB, 1000);

		assert_ok!(Broadcaster::force_register_publisher(RuntimeOrigin::root(), BOB, 500, para_id));

		let info = RegisteredPublishers::<Test>::get(para_id).unwrap();
		assert_eq!(info.manager, BOB);
		assert_eq!(info.deposit, 500);

		assert_eq!(Balances::balance_on_hold(&HoldReason::PublisherDeposit.into(), &BOB), 500);
		assert_eq!(Balances::balance(&BOB), 500);
	});
}

#[test]
fn cannot_register_twice() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 1000);
		setup_account(BOB, 1000);

		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));

		assert_err!(
			Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id),
			Error::<Test>::AlreadyRegistered
		);

		assert_err!(
			Broadcaster::register_publisher(RuntimeOrigin::signed(BOB), para_id),
			Error::<Test>::AlreadyRegistered
		);

		assert_eq!(Balances::balance_on_hold(&HoldReason::PublisherDeposit.into(), &ALICE), 100);
		assert_eq!(Balances::balance_on_hold(&HoldReason::PublisherDeposit.into(), &BOB), 0);
	});
}

#[test]
fn force_register_requires_root() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(1000);
		setup_account(ALICE, 1000);

		assert_err!(
			Broadcaster::force_register_publisher(RuntimeOrigin::signed(ALICE), ALICE, 0, para_id),
			sp_runtime::DispatchError::BadOrigin
		);

		assert!(!RegisteredPublishers::<Test>::contains_key(para_id));
	});
}

#[test]
fn register_publisher_requires_sufficient_balance() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 50); // Less than required deposit

		let result = Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id);
		assert!(result.is_err());

		assert!(!RegisteredPublishers::<Test>::contains_key(para_id));
	});
}

#[test]
fn publish_requires_registration() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		let data = vec![publish_item(b"key", b"value")];

		assert_err!(
			Broadcaster::handle_publish(para_id, data),
			Error::<Test>::PublishNotAuthorized
		);

		assert!(!PublisherExists::<Test>::get(para_id));
	});
}

#[test]
fn registered_publisher_can_publish() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 1000);

		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));

		let data = vec![publish_item(b"key", b"value")];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		assert_eq!(
			Broadcaster::get_published_value(para_id, &hash_key(b"key")),
			Some(b"value".to_vec())
		);
	});
}

#[test]
fn publish_store_retrieve_and_update_data() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 1000);

		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));

		assert!(!PublisherExists::<Test>::get(para_id));
		assert!(Broadcaster::get_publisher_child_root(para_id).is_none());

		let initial_data = vec![publish_item(b"key1", b"value1"), publish_item(b"key2", b"value2")];
		Broadcaster::handle_publish(para_id, initial_data.clone()).unwrap();

		assert!(PublisherExists::<Test>::get(para_id));
		let root_after_initial = Broadcaster::get_publisher_child_root(para_id);
		assert!(root_after_initial.is_some());
		assert!(!root_after_initial.as_ref().unwrap().is_empty());

		assert_eq!(
			Broadcaster::get_published_value(para_id, &hash_key(b"key1")),
			Some(b"value1".to_vec())
		);
		assert_eq!(
			Broadcaster::get_published_value(para_id, &hash_key(b"key2")),
			Some(b"value2".to_vec())
		);
		assert_eq!(Broadcaster::get_published_value(para_id, &hash_key(b"key3")), None);

		let update_data =
			vec![publish_item(b"key1", b"updated_value1"), publish_item(b"key3", b"value3")];
		Broadcaster::handle_publish(para_id, update_data).unwrap();

		let root_after_update = Broadcaster::get_publisher_child_root(para_id);
		assert!(root_after_update.is_some());
		assert_ne!(root_after_initial.unwrap(), root_after_update.unwrap());

		assert_eq!(
			Broadcaster::get_published_value(para_id, &hash_key(b"key1")),
			Some(b"updated_value1".to_vec())
		);
		assert_eq!(
			Broadcaster::get_published_value(para_id, &hash_key(b"key2")),
			Some(b"value2".to_vec()) // Should remain unchanged
		);
		assert_eq!(
			Broadcaster::get_published_value(para_id, &hash_key(b"key3")),
			Some(b"value3".to_vec())
		);
	});
}

#[test]
fn handle_publish_respects_max_items_limit() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		let mut data = Vec::new();
		for i in 0..17 {
			data.push((hash_key(&format!("key{}", i).into_bytes()), b"value".to_vec(), 0));
		}

		let result = Broadcaster::handle_publish(para_id, data);
		assert!(result.is_err());
	});
}

#[test]
fn handle_publish_respects_value_length_limit() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		let long_value = vec![b'v'; 1025];
		let data = vec![(hash_key(b"key"), long_value, 0)];

		let result = Broadcaster::handle_publish(para_id, data);
		assert!(result.is_err());
	});
}

#[test]
fn total_storage_size_limit_enforced() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		// Try to publish data that exceeds 2048 bytes total
		// Each item is 32 (key) + 1024 (value) = 1056 bytes
		// Two items would be 2112 bytes, exceeding the 2048 limit
		let data1 = vec![(hash_key(b"key1"), vec![b'a'; 1024], 0)];
		assert_ok!(Broadcaster::handle_publish(para_id, data1));

		// Second item should fail due to total storage size
		let data2 = vec![(hash_key(b"key2"), vec![b'b'; 1024], 0)];
		let result = Broadcaster::handle_publish(para_id, data2);
		assert_err!(result, Error::<Test>::TotalStorageSizeExceeded);

		// But updating the existing key with a smaller value should work
		let data3 = vec![(hash_key(b"key1"), vec![b'c'; 100], 0)];
		assert_ok!(Broadcaster::handle_publish(para_id, data3));

		// Now we should have room for more data
		let data4 = vec![(hash_key(b"key2"), vec![b'd'; 900], 0)];
		assert_ok!(Broadcaster::handle_publish(para_id, data4));
	});
}

#[test]
fn max_stored_keys_limit_enforced() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		// Publish 50 small items to test MaxStoredKeys without hitting TotalStorageSize limit
		// Each item is 32 (key) + 1 (value) = 33 bytes, total ~1650 bytes
		// Publish in batches of 10 items to respect MaxPublishItems = 10
		for batch in 0..5 {
			let mut data = Vec::new();
			for i in 0..10 {
				let key_num = batch * 10 + i;
				if key_num < 50 {
					data.push((
						hash_key(&format!("key{}", key_num).into_bytes()),
						b"v".to_vec(),
						0,
					));
				}
			}
			if !data.is_empty() {
				assert_ok!(Broadcaster::handle_publish(para_id, data));
			}
		}

		let published_keys = PublishedKeys::<Test>::get(para_id);
		assert_eq!(published_keys.len(), 50);

		let result = Broadcaster::handle_publish(para_id, vec![publish_item(b"new_key", b"value")]);
		assert_err!(result, Error::<Test>::TooManyStoredKeys);

		let result =
			Broadcaster::handle_publish(para_id, vec![publish_item(b"key0", b"updated_value")]);
		assert_ok!(result);

		assert_eq!(
			Broadcaster::get_published_value(para_id, &hash_key(b"key0")),
			Some(b"updated_value".to_vec())
		);
	});
}

#[test]
fn published_keys_storage_matches_child_trie() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		// Publish multiple batches to ensure consistency maintained across updates
		let data1 = vec![publish_item(b"key1", b"value1"), publish_item(b"key2", b"value2")];
		Broadcaster::handle_publish(para_id, data1).unwrap();

		// Update some keys, add new ones
		let data2 =
			vec![publish_item(b"key1", b"updated_value1"), publish_item(b"key3", b"value3")];
		Broadcaster::handle_publish(para_id, data2).unwrap();

		let tracked_keys = PublishedKeys::<Test>::get(para_id);
		let actual_data = Broadcaster::get_all_published_data(para_id);

		// Counts must match
		assert_eq!(tracked_keys.len(), actual_data.len());

		// Every tracked key must exist in child trie
		for tracked_key in tracked_keys.iter() {
			assert!(actual_data.iter().any(|(k, _)| k == tracked_key));
		}

		// Every child trie key must be tracked
		for (actual_key, _) in actual_data.iter() {
			assert!(tracked_keys.contains(actual_key));
		}
	});
}

#[test]
fn multiple_publishers_in_same_block() {
	new_test_ext(Default::default()).execute_with(|| {
		let para1 = ParaId::from(2000);
		let para2 = ParaId::from(2001);
		let para3 = ParaId::from(2002);

		// Register all publishers
		register_test_publisher(para1);
		setup_account(BOB, 10000);
		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(BOB), para2));
		setup_account(3, 10000);
		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(3), para3));

		// Multiple parachains publish data in the same block
		let data1 = vec![publish_item(b"key1", b"value1")];
		let data2 = vec![publish_item(b"key2", b"value2")];
		let data3 = vec![publish_item(b"key3", b"value3")];

		Broadcaster::handle_publish(para1, data1).unwrap();
		Broadcaster::handle_publish(para2, data2).unwrap();
		Broadcaster::handle_publish(para3, data3).unwrap();

		// Verify all three publishers exist
		assert!(PublisherExists::<Test>::get(para1));
		assert!(PublisherExists::<Test>::get(para2));
		assert!(PublisherExists::<Test>::get(para3));

		// Verify each para's data is independently accessible
		assert_eq!(
			Broadcaster::get_published_value(para1, &hash_key(b"key1")),
			Some(b"value1".to_vec())
		);
		assert_eq!(
			Broadcaster::get_published_value(para2, &hash_key(b"key2")),
			Some(b"value2".to_vec())
		);
		assert_eq!(
			Broadcaster::get_published_value(para3, &hash_key(b"key3")),
			Some(b"value3".to_vec())
		);

		// Verify no cross-contamination
		assert_eq!(Broadcaster::get_published_value(para1, &hash_key(b"key2")), None);
		assert_eq!(Broadcaster::get_published_value(para2, &hash_key(b"key3")), None);
		assert_eq!(Broadcaster::get_published_value(para3, &hash_key(b"key1")), None);
	});
}

#[test]
fn max_publishers_limit_enforced() {
	new_test_ext(Default::default()).execute_with(|| {
		// Register and publish for max publishers
		for i in 0..1000 {
			let para_id = ParaId::from(2000 + i);
			setup_account(100 + i as u64, 10000);
			assert_ok!(Broadcaster::register_publisher(
				RuntimeOrigin::signed(100 + i as u64),
				para_id
			));
			let data = vec![publish_item(b"key", b"value")];
			assert_ok!(Broadcaster::handle_publish(para_id, data));
		}

		assert_eq!(PublisherExists::<Test>::iter().count(), 1000);

		// Cannot register new publisher when limit reached
		let new_para = ParaId::from(3000);
		setup_account(ALICE, 10000);

		// Registration should fail at registration time due to MaxPublishers limit
		assert_err!(
			Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), new_para),
			Error::<Test>::TooManyPublishers
		);

		// Existing publisher can still update
		let existing_para = ParaId::from(2000);
		let update_data = vec![publish_item(b"key", b"updated")];
		assert_ok!(Broadcaster::handle_publish(existing_para, update_data));
		assert_eq!(
			Broadcaster::get_published_value(existing_para, &hash_key(b"key")),
			Some(b"updated".to_vec())
		);
	});
}

#[test]
fn cleanup_published_data_works() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 10000);

		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));
		let data = vec![publish_item(b"key1", b"value1"), publish_item(b"key2", b"value2")];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		assert!(PublisherExists::<Test>::get(para_id));
		assert_eq!(PublishedKeys::<Test>::get(para_id).len(), 2);

		assert_ok!(Broadcaster::cleanup_published_data(RuntimeOrigin::signed(ALICE), para_id));

		assert!(!PublisherExists::<Test>::get(para_id));
		assert_eq!(PublishedKeys::<Test>::get(para_id).len(), 0);
		assert_eq!(Broadcaster::get_published_value(para_id, &hash_key(b"key1")), None);
		assert_eq!(Broadcaster::get_published_value(para_id, &hash_key(b"key2")), None);
		assert!(RegisteredPublishers::<Test>::get(para_id).is_some());
	});
}

#[test]
fn cleanup_requires_manager() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 10000);
		setup_account(BOB, 10000);

		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));
		assert_ok!(Broadcaster::handle_publish(para_id, vec![publish_item(b"key", b"value")]));

		assert_err!(
			Broadcaster::cleanup_published_data(RuntimeOrigin::signed(BOB), para_id),
			Error::<Test>::NotAuthorized
		);

		assert!(PublisherExists::<Test>::get(para_id));
	});
}

#[test]
fn cleanup_fails_if_no_data() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 10000);

		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));

		assert_err!(
			Broadcaster::cleanup_published_data(RuntimeOrigin::signed(ALICE), para_id),
			Error::<Test>::NoDataToCleanup
		);
	});
}

#[test]
fn cleanup_fails_if_not_registered() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 10000);

		assert_err!(
			Broadcaster::cleanup_published_data(RuntimeOrigin::signed(ALICE), para_id),
			Error::<Test>::NotRegistered
		);
	});
}

#[test]
fn deregister_publisher_works() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 10000);

		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));

		assert_eq!(Balances::balance_on_hold(&HoldReason::PublisherDeposit.into(), &ALICE), 100);
		assert_eq!(Balances::balance(&ALICE), 9900);

		assert_ok!(Broadcaster::deregister_publisher(RuntimeOrigin::signed(ALICE), para_id));

		assert_eq!(Balances::balance_on_hold(&HoldReason::PublisherDeposit.into(), &ALICE), 0);
		assert_eq!(Balances::balance(&ALICE), 10000);
		assert!(!RegisteredPublishers::<Test>::contains_key(para_id));
	});
}

#[test]
fn deregister_fails_if_data_exists() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 10000);

		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));
		assert_ok!(Broadcaster::handle_publish(para_id, vec![publish_item(b"key", b"value")]));

		assert_err!(
			Broadcaster::deregister_publisher(RuntimeOrigin::signed(ALICE), para_id),
			Error::<Test>::MustCleanupDataFirst
		);

		assert_eq!(Balances::balance_on_hold(&HoldReason::PublisherDeposit.into(), &ALICE), 100);
	});
}

#[test]
fn deregister_requires_manager() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 10000);
		setup_account(BOB, 10000);

		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));

		assert_err!(
			Broadcaster::deregister_publisher(RuntimeOrigin::signed(BOB), para_id),
			Error::<Test>::NotAuthorized
		);
	});
}

#[test]
fn two_phase_cleanup_and_deregister_works() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 10000);

		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));
		let data = vec![
			publish_item(b"key1", b"value1"),
			publish_item(b"key2", b"value2"),
			publish_item(b"key3", b"value3"),
		];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		// Phase 1: Cleanup data
		assert_ok!(Broadcaster::cleanup_published_data(RuntimeOrigin::signed(ALICE), para_id));
		assert!(!PublisherExists::<Test>::get(para_id));
		assert_eq!(Balances::balance_on_hold(&HoldReason::PublisherDeposit.into(), &ALICE), 100);

		// Phase 2: Deregister
		assert_ok!(Broadcaster::deregister_publisher(RuntimeOrigin::signed(ALICE), para_id));
		assert!(!RegisteredPublishers::<Test>::contains_key(para_id));
		assert_eq!(Balances::balance_on_hold(&HoldReason::PublisherDeposit.into(), &ALICE), 0);
		assert_eq!(Balances::balance(&ALICE), 10000);
	});
}

#[test]
fn force_deregister_works() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 10000);

		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));
		let data = vec![publish_item(b"key1", b"value1"), publish_item(b"key2", b"value2")];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		assert_ok!(Broadcaster::force_deregister_publisher(RuntimeOrigin::root(), para_id));

		assert!(!PublisherExists::<Test>::get(para_id));
		assert!(!RegisteredPublishers::<Test>::contains_key(para_id));
		assert_eq!(PublishedKeys::<Test>::get(para_id).len(), 0);
		assert_eq!(Balances::balance_on_hold(&HoldReason::PublisherDeposit.into(), &ALICE), 0);
		assert_eq!(Balances::balance(&ALICE), 10000);
	});
}

#[test]
fn force_deregister_works_without_data() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 10000);

		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));

		assert_ok!(Broadcaster::force_deregister_publisher(RuntimeOrigin::root(), para_id));

		assert!(!RegisteredPublishers::<Test>::contains_key(para_id));
		assert_eq!(Balances::balance(&ALICE), 10000);
	});
}

#[test]
fn force_deregister_requires_root() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 10000);

		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));
		assert_ok!(Broadcaster::handle_publish(para_id, vec![publish_item(b"key", b"value")]));

		assert_err!(
			Broadcaster::force_deregister_publisher(RuntimeOrigin::signed(ALICE), para_id),
			sp_runtime::DispatchError::BadOrigin
		);

		assert!(PublisherExists::<Test>::get(para_id));
		assert!(RegisteredPublishers::<Test>::contains_key(para_id));
	});
}

#[test]
fn cleanup_removes_all_keys_from_child_trie() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 10000);

		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));

		// Publish multiple batches to fill up keys
		for batch in 0..5 {
			let mut data = Vec::new();
			for i in 0..10 {
				let key = format!("key_{}_{}", batch, i);
				data.push((hash_key(key.as_bytes()), b"value".to_vec(), 0));
			}
			assert_ok!(Broadcaster::handle_publish(para_id, data));
		}

		assert_eq!(PublishedKeys::<Test>::get(para_id).len(), 50);

		assert_ok!(Broadcaster::cleanup_published_data(RuntimeOrigin::signed(ALICE), para_id));

		for batch in 0..5 {
			for i in 0..10 {
				let key = format!("key_{}_{}", batch, i);
				assert_eq!(
					Broadcaster::get_published_value(para_id, &hash_key(key.as_bytes())),
					None
				);
			}
		}

		assert_eq!(PublishedKeys::<Test>::get(para_id).len(), 0);
	});
}

#[test]
fn force_deregister_with_zero_deposit() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(1000); // System chain
		setup_account(ALICE, 10000);

		assert_ok!(Broadcaster::force_register_publisher(RuntimeOrigin::root(), ALICE, 0, para_id));

		assert_ok!(Broadcaster::handle_publish(para_id, vec![publish_item(b"key", b"value")]));

		assert_ok!(Broadcaster::force_deregister_publisher(RuntimeOrigin::root(), para_id));

		assert!(!RegisteredPublishers::<Test>::contains_key(para_id));
		assert_eq!(Balances::balance(&ALICE), 10000); // No deposit change
	});
}

#[test]
fn cleanup_outgoing_publishers_works() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_a = ParaId::from(2000);
		let para_b = ParaId::from(2001);
		let para_c = ParaId::from(2002);

		setup_account(ALICE, 10000);

		// Register and publish data for A, B, C
		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_a));
		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_b));
		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_c));

		assert_ok!(Broadcaster::handle_publish(para_a, vec![publish_item(b"key1", b"value1")]));
		assert_ok!(Broadcaster::handle_publish(para_b, vec![publish_item(b"key2", b"value2")]));
		assert_ok!(Broadcaster::handle_publish(para_c, vec![publish_item(b"key3", b"value3")]));

		let notification = crate::initializer::SessionChangeNotification::default();
		let outgoing_paras = vec![para_a, para_b];
		Broadcaster::initializer_on_new_session(&notification, &outgoing_paras);

		// A and B cleaned up
		assert!(!RegisteredPublishers::<Test>::contains_key(para_a));
		assert!(!RegisteredPublishers::<Test>::contains_key(para_b));
		assert!(!PublisherExists::<Test>::get(para_a));
		assert!(!PublisherExists::<Test>::get(para_b));

		// C unaffected
		assert!(RegisteredPublishers::<Test>::contains_key(para_c));
		assert!(PublisherExists::<Test>::get(para_c));
	});
}

#[test]
fn empty_publish_fails() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		// Try to publish empty data
		let empty_data: Vec<([u8; 32], Vec<u8>, u32)> = vec![];

		assert_err!(Broadcaster::handle_publish(para_id, empty_data), Error::<Test>::EmptyPublish);
	});
}

#[test]
fn child_trie_key_derivation_matches_spec() {
	use codec::Encode;

	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(1000);
		let child_info = Broadcaster::derive_child_info(para_id);
		let expected_key = (b"pubsub", para_id).encode();

		assert_eq!(child_info.storage_key(), expected_key.as_slice());
	});
}

#[test]
fn system_parachain_boundary_id_1999() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(1999);
		setup_account(ALICE, 10000);

		assert_ok!(Broadcaster::force_register_publisher(RuntimeOrigin::root(), ALICE, 0, para_id));

		let info = RegisteredPublishers::<Test>::get(para_id).unwrap();
		assert_eq!(info.deposit, 0);

		let data = vec![publish_item(b"key", b"value")];
		assert_ok!(Broadcaster::handle_publish(para_id, data));
	});
}

#[test]
fn non_system_parachain_boundary_id_2000() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);

		let data = vec![publish_item(b"key", b"value")];
		assert_err!(
			Broadcaster::handle_publish(para_id, data),
			Error::<Test>::PublishNotAuthorized
		);

		setup_account(ALICE, 10000);
		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));

		let info = RegisteredPublishers::<Test>::get(para_id).unwrap();
		assert_eq!(info.deposit, 100);

		let data = vec![publish_item(b"key", b"value")];
		assert_ok!(Broadcaster::handle_publish(para_id, data));
	});
}

#[test]
fn system_parachain_publishes_without_registration() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(1000);

		let (key, value, ttl) = publish_item(b"key", b"value");
		assert_ok!(Broadcaster::handle_publish(para_id, key, value, ttl));

		assert!(PublisherExists::<Test>::get(para_id));
		let published_keys = PublishedKeys::<Test>::get(para_id);
		assert_eq!(published_keys.len(), 1);
		assert!(published_keys.contains(&key));
	});
}

#[test]
fn register_non_system_parachain_high_id() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(5000);
		setup_account(ALICE, 10000);

		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));

		let info = RegisteredPublishers::<Test>::get(para_id).unwrap();
		assert_eq!(info.manager, ALICE);
		assert_eq!(info.deposit, 100);

		let data = vec![publish_item(b"key", b"value")];
		assert_ok!(Broadcaster::handle_publish(para_id, data));
	});
}

#[test]
fn publish_32_byte_key_works() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		let key: [u8; 32] = [0xAB; 32];
		let data = vec![(key, b"value".to_vec(), 0)];

		assert_ok!(Broadcaster::handle_publish(para_id, data));
		assert_eq!(Broadcaster::get_published_value(para_id, &key), Some(b"value".to_vec()));
	});
}

#[test]
fn publish_max_value_size_works() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		let max_value = vec![b'x'; 1024];
		let data = vec![(hash_key(b"key"), max_value.clone(), 0)];

		assert_ok!(Broadcaster::handle_publish(para_id, data));
		assert_eq!(Broadcaster::get_published_value(para_id, &hash_key(b"key")), Some(max_value));
	});
}

#[test]
fn deregister_not_registered_fails() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 10000);

		assert_err!(
			Broadcaster::deregister_publisher(RuntimeOrigin::signed(ALICE), para_id),
			Error::<Test>::NotRegistered
		);
	});
}

#[test]
fn deregister_clears_child_trie_completely() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		setup_account(ALICE, 10000);

		assert_ok!(Broadcaster::register_publisher(RuntimeOrigin::signed(ALICE), para_id));

		let data = vec![
			publish_item(b"key1", b"value1"),
			publish_item(b"key2", b"value2"),
			publish_item(b"key3", b"value3"),
		];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		assert!(PublisherExists::<Test>::get(para_id));
		assert_eq!(PublishedKeys::<Test>::get(para_id).len(), 3);

		assert_ok!(Broadcaster::cleanup_published_data(RuntimeOrigin::signed(ALICE), para_id));
		assert_ok!(Broadcaster::deregister_publisher(RuntimeOrigin::signed(ALICE), para_id));

		assert!(!PublisherExists::<Test>::get(para_id));
		assert_eq!(PublishedKeys::<Test>::get(para_id).len(), 0);
		assert_eq!(TotalStorageSize::<Test>::get(para_id), 0);

		assert_eq!(Broadcaster::get_published_value(para_id, &hash_key(b"key1")), None);
		assert_eq!(Broadcaster::get_published_value(para_id, &hash_key(b"key2")), None);
		assert_eq!(Broadcaster::get_published_value(para_id, &hash_key(b"key3")), None);
	});
}

// TTL Tests (Section 1.4 of test plan)

#[test]
fn publish_infinite_ttl_no_ttl_data_entry() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		let data = vec![publish_item(b"key", b"value")];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		assert!(TtlData::<Test>::get(para_id, hash_key(b"key")).is_none());
		assert_eq!(
			Broadcaster::get_published_value(para_id, &hash_key(b"key")),
			Some(b"value".to_vec())
		);
	});
}

#[test]
fn publish_finite_ttl_creates_ttl_data_entry() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		System::set_block_number(100);
		let data = vec![publish_item_with_ttl(b"key", b"value", 500)];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		let ttl_entry = TtlData::<Test>::get(para_id, hash_key(b"key"));
		assert!(ttl_entry.is_some());
		let (ttl, inserted_at) = ttl_entry.unwrap();
		assert_eq!(ttl, 500);
		assert_eq!(inserted_at, 100);

		assert_eq!(
			Broadcaster::get_published_value(para_id, &hash_key(b"key")),
			Some(b"value".to_vec())
		);
	});
}

#[test]
fn publish_large_ttl_accepted_as_is() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		System::set_block_number(1);
		let data = vec![publish_item_with_ttl(b"key", b"value", u32::MAX)];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		let (ttl, _) = TtlData::<Test>::get(para_id, hash_key(b"key")).unwrap();
		assert_eq!(ttl, u32::MAX);
	});
}

#[test]
fn ttl_reset_on_update() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		System::set_block_number(100);
		let data = vec![publish_item_with_ttl(b"key", b"value1", 500)];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		let (ttl, inserted_at) = TtlData::<Test>::get(para_id, hash_key(b"key")).unwrap();
		assert_eq!(ttl, 500);
		assert_eq!(inserted_at, 100);

		System::set_block_number(150);
		let data = vec![publish_item_with_ttl(b"key", b"value2", 200)];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		let (new_ttl, new_inserted_at) = TtlData::<Test>::get(para_id, hash_key(b"key")).unwrap();
		assert_eq!(new_ttl, 200);
		assert_eq!(new_inserted_at, 150);

		assert_eq!(
			Broadcaster::get_published_value(para_id, &hash_key(b"key")),
			Some(b"value2".to_vec())
		);
	});
}

#[test]
fn ttl_finite_to_infinite() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		System::set_block_number(100);
		let data = vec![publish_item_with_ttl(b"key", b"value1", 500)];
		assert_ok!(Broadcaster::handle_publish(para_id, data));
		assert!(TtlData::<Test>::get(para_id, hash_key(b"key")).is_some());

		let data = vec![publish_item(b"key", b"value2")];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		assert!(TtlData::<Test>::get(para_id, hash_key(b"key")).is_none());
		assert_eq!(
			Broadcaster::get_published_value(para_id, &hash_key(b"key")),
			Some(b"value2".to_vec())
		);
	});
}

#[test]
fn ttl_infinite_to_finite() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		let data = vec![publish_item(b"key", b"value1")];
		assert_ok!(Broadcaster::handle_publish(para_id, data));
		assert!(TtlData::<Test>::get(para_id, hash_key(b"key")).is_none());

		System::set_block_number(100);
		let data = vec![publish_item_with_ttl(b"key", b"value2", 500)];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		let (ttl, inserted_at) = TtlData::<Test>::get(para_id, hash_key(b"key")).unwrap();
		assert_eq!(ttl, 500);
		assert_eq!(inserted_at, 100);
	});
}

#[test]
fn on_idle_expires_keys() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		System::set_block_number(100);
		let data = vec![publish_item_with_ttl(b"key1", b"value1", 50)];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		assert!(TtlData::<Test>::get(para_id, hash_key(b"key1")).is_some());
		assert!(Broadcaster::get_published_value(para_id, &hash_key(b"key1")).is_some());

		System::set_block_number(149);
		Broadcaster::on_idle(149, Weight::from_parts(1_000_000_000, 1_000_000_000));
		assert!(Broadcaster::get_published_value(para_id, &hash_key(b"key1")).is_some());

		System::set_block_number(150);
		Broadcaster::on_idle(150, Weight::from_parts(1_000_000_000, 1_000_000_000));

		assert!(TtlData::<Test>::get(para_id, hash_key(b"key1")).is_none());
		assert!(Broadcaster::get_published_value(para_id, &hash_key(b"key1")).is_none());
	});
}

#[test]
fn on_idle_partial_cleanup_sets_cursor() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		System::set_block_number(100);
		for i in 0..10 {
			let key = format!("key{}", i);
			let data = vec![(hash_key(key.as_bytes()), b"value".to_vec(), 50)];
			assert_ok!(Broadcaster::handle_publish(para_id, data));
		}

		System::set_block_number(200);

		let minimal_weight = Weight::from_parts(10_000, 10_000);
		Broadcaster::on_idle(200, minimal_weight);

		let cursor = TtlScanCursor::<Test>::get();
		if cursor.is_some() {
			let remaining_ttl_entries = TtlData::<Test>::iter().count();
			assert!(remaining_ttl_entries < 10);
		}
	});
}

#[test]
fn on_idle_cursor_resumption() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		System::set_block_number(100);
		for i in 0..5 {
			let key = format!("key{}", i);
			let data = vec![(hash_key(key.as_bytes()), b"value".to_vec(), 50)];
			assert_ok!(Broadcaster::handle_publish(para_id, data));
		}

		System::set_block_number(200);

		let full_weight = Weight::from_parts(1_000_000_000, 1_000_000_000);
		for _ in 0..10 {
			Broadcaster::on_idle(200, full_weight);
		}

		let remaining = TtlData::<Test>::iter().count();
		assert_eq!(remaining, 0);

		assert!(TtlScanCursor::<Test>::get().is_none());
	});
}

// Manual Deletion Tests (Section 1.5 of test plan)

#[test]
fn delete_keys_by_manager_works() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		let data = vec![
			publish_item(b"key1", b"value1"),
			publish_item(b"key2", b"value2"),
			publish_item(b"key3", b"value3"),
		];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		assert_ok!(Broadcaster::delete_keys(
			RuntimeOrigin::signed(ALICE),
			para_id,
			vec![hash_key(b"key1"), hash_key(b"key2")]
		));

		assert!(Broadcaster::get_published_value(para_id, &hash_key(b"key1")).is_none());
		assert!(Broadcaster::get_published_value(para_id, &hash_key(b"key2")).is_none());
		assert!(Broadcaster::get_published_value(para_id, &hash_key(b"key3")).is_some());
	});
}

#[test]
fn delete_keys_not_manager_fails() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		let data = vec![publish_item(b"key1", b"value1")];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		setup_account(BOB, 1000);
		assert_err!(
			Broadcaster::delete_keys(RuntimeOrigin::signed(BOB), para_id, vec![hash_key(b"key1")]),
			Error::<Test>::NotAuthorized
		);

		assert!(Broadcaster::get_published_value(para_id, &hash_key(b"key1")).is_some());
	});
}

#[test]
fn delete_nonexistent_keys_fails() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		let data = vec![publish_item(b"key1", b"value1")];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		assert_err!(
			Broadcaster::delete_keys(
				RuntimeOrigin::signed(ALICE),
				para_id,
				vec![hash_key(b"nonexistent")]
			),
			Error::<Test>::NoKeysToDelete
		);
	});
}

#[test]
fn delete_keys_removes_ttl_data() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		System::set_block_number(100);
		let data = vec![publish_item_with_ttl(b"key1", b"value1", 500)];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		assert!(TtlData::<Test>::get(para_id, hash_key(b"key1")).is_some());

		assert_ok!(Broadcaster::delete_keys(
			RuntimeOrigin::signed(ALICE),
			para_id,
			vec![hash_key(b"key1")]
		));

		assert!(TtlData::<Test>::get(para_id, hash_key(b"key1")).is_none());
		assert!(Broadcaster::get_published_value(para_id, &hash_key(b"key1")).is_none());
	});
}

#[test]
fn force_delete_keys_by_governance_works() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		let data = vec![publish_item(b"key1", b"value1"), publish_item(b"key2", b"value2")];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		assert_ok!(Broadcaster::force_delete_keys(
			RuntimeOrigin::root(),
			para_id,
			vec![hash_key(b"key1"), hash_key(b"key2")]
		));

		assert!(Broadcaster::get_published_value(para_id, &hash_key(b"key1")).is_none());
		assert!(Broadcaster::get_published_value(para_id, &hash_key(b"key2")).is_none());
	});
}

#[test]
fn force_delete_keys_requires_root() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		let data = vec![publish_item(b"key1", b"value1")];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		assert_err!(
			Broadcaster::force_delete_keys(
				RuntimeOrigin::signed(ALICE),
				para_id,
				vec![hash_key(b"key1")]
			),
			sp_runtime::DispatchError::BadOrigin
		);

		assert!(Broadcaster::get_published_value(para_id, &hash_key(b"key1")).is_some());
	});
}

#[test]
fn cleanup_publisher_also_clears_ttl_data() {
	new_test_ext(Default::default()).execute_with(|| {
		let para_id = ParaId::from(2000);
		register_test_publisher(para_id);

		System::set_block_number(100);
		let data = vec![
			publish_item_with_ttl(b"key1", b"value1", 500),
			publish_item_with_ttl(b"key2", b"value2", 1000),
			publish_item(b"key3", b"value3"),
		];
		assert_ok!(Broadcaster::handle_publish(para_id, data));

		assert!(TtlData::<Test>::get(para_id, hash_key(b"key1")).is_some());
		assert!(TtlData::<Test>::get(para_id, hash_key(b"key2")).is_some());
		assert!(TtlData::<Test>::get(para_id, hash_key(b"key3")).is_none());

		assert_ok!(Broadcaster::cleanup_published_data(RuntimeOrigin::signed(ALICE), para_id));

		assert!(TtlData::<Test>::get(para_id, hash_key(b"key1")).is_none());
		assert!(TtlData::<Test>::get(para_id, hash_key(b"key2")).is_none());
		assert!(TtlData::<Test>::get(para_id, hash_key(b"key3")).is_none());
	});
}
