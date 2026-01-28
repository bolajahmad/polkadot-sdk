# Test Plan: Pub-Sub System

This document provides a comprehensive test plan for the pub-sub system, including all edge cases that must be tested.

## Test Categories

1. **Unit Tests** - Individual component testing
2. **Integration Tests** - Cross-component testing within a single runtime
3. **Zombienet Tests** - End-to-end multi-chain testing

---

## 1. Broadcaster Pallet Unit Tests (Relay Chain)

### 1.1 Publisher Registration

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `register_non_system_parachain_success` | Register parachain ID 2000 (first non-system) with sufficient balance | Deposit held, `PublisherRegistered` event, can publish |
| `register_non_system_parachain_high_id` | Register parachain ID 5000 with sufficient balance | Success |
| `register_public_parachain_insufficient_balance` | Register with balance < deposit | Error: `InsufficientBalance` |
| `register_already_registered` | Register same parachain twice | Error: `AlreadyRegistered` |
| `register_max_publishers_reached` | Register when `MaxPublishers` limit reached | Error: `TooManyPublishers` |
| `system_parachain_publishes_without_registration` | System parachain (ID 1000 < 2000) publishes without registration | Success, no deposit required |
| `system_parachain_boundary` | Parachain ID 1999 (last system) publishes without registration | Success |
| `non_system_parachain_boundary` | Parachain ID 2000 (first non-system) requires registration | Error if not registered |
| `force_register_by_root` | Root origin force-registers parachain | Success, zero deposit |
| `force_register_by_non_root` | Non-root tries force-register | Error: `BadOrigin` |

### 1.2 Publisher Deregistration

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `deregister_success` | Deregister registered publisher | All data deleted, deposit released, `PublisherDeregistered` event |
| `deregister_not_registered` | Deregister unregistered parachain | Error: `NotRegistered` |
| `deregister_wrong_manager` | Wrong account tries to deregister | Error: `NotManager` |
| `force_deregister_by_governance` | Root force-deregisters publisher | Data deleted, deposit slashed/returned per config |
| `deregister_clears_child_trie` | Verify child trie fully cleared on deregister | No keys remain in child trie |
| `deregister_clears_ttl_data` | Verify TtlData cleared on deregister | No TtlData entries for parachain |

### 1.3 Publish Operations

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `publish_registered_non_system_parachain` | Registered parachain ID 2000 publishes | Data stored, `DataPublished` event |
| `publish_system_parachain_id_1000` | System parachain ID 1000 publishes | Success without registration |
| `publish_system_parachain_id_1999` | System parachain ID 1999 (boundary) publishes | Success without registration |
| `publish_unregistered_non_system_parachain` | Unregistered parachain ID 2000 (boundary) publishes | Error: `NotRegistered` |
| `publish_unregistered_non_system_parachain_high_id` | Unregistered parachain ID 5000 publishes | Error: `NotRegistered` |
| `publish_32_byte_key` | Publish with exactly 32-byte key | Success |
| `publish_max_value_size` | Publish value at `MaxValueLength` | Success |
| `publish_value_too_large` | Publish value > `MaxValueLength` | Error: `ValueTooLarge` |
| `publish_max_keys_reached` | Publish when `MaxStoredKeys` reached | Error: `TooManyKeys` |
| `publish_total_storage_exceeded` | Publish when `MaxTotalStorageSize` would be exceeded | Error: `TotalStorageSizeExceeded` |
| `publish_update_existing_key` | Update value for existing key | Value updated, storage size adjusted |
| `child_trie_key_derivation` | Verify child trie key format | Key equals `(b"pubsub", ParaId).encode()` |
| `ttl_data_stored_separately` | Verify TtlData exists independently | TtlData queryable without child trie access |

### 1.4 TTL Logic

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `publish_infinite_ttl` | Publish with TTL = 0 | No TtlData entry, never expires |
| `publish_finite_ttl` | Publish with TTL > 0 | TtlData entry created with (ttl, when_inserted) |
| `publish_large_ttl` | Publish with very large TTL (e.g., u32::MAX) | TTL accepted as-is, no capping |
| `ttl_reset_on_update` | Re-publish existing key with new TTL | TTL reset to new value from current block |
| `ttl_finite_to_infinite` | Update key from finite TTL to TTL = 0 | TtlData entry removed |
| `ttl_infinite_to_finite` | Update key from TTL = 0 to finite TTL | TtlData entry created |
| `on_idle_expires_keys` | Keys with expired TTL deleted in on_idle | Keys deleted, `KeyExpired` events |
| `on_idle_partial_cleanup` | More expired keys than `MaxTtlScansPerIdle` | Cursor set, partial cleanup |
| `on_idle_cursor_resumption` | Resume from cursor in next block | Continue cleanup from cursor position |
| `on_idle_cursor_wrap_around` | Cursor reaches end, wraps to beginning | Full scan completed over multiple blocks |

### 1.5 Manual Deletion

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `delete_keys_by_owner` | Publisher deletes own keys | Keys deleted, `KeysDeleted` event |
| `delete_keys_not_owner` | Non-owner tries to delete | Error: `NotOwner` |
| `delete_nonexistent_keys` | Delete keys that don't exist | No-op or partial success |
| `delete_keys_removes_ttl_data` | Delete key with finite TTL | TtlData entry also removed |
| `force_delete_keys_by_governance` | Root deletes any keys | Keys deleted, `KeysForcedDeleted` event |

### 1.6 Parachain Offboarding

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `offboarding_cleans_data` | Parachain offboarded from relay | All published data and registration cleared |

---

## 2. XCM Publish Instruction Unit Tests

**Fee Model:** The `Publish` instruction uses a dedicated `AllowPublishFrom<T>` barrier (similar to `AllowSubscriptionsFrom`) that only allows messages containing just the `Publish` instruction. This enables free execution for publishing without allowing unpaid execution for arbitrary XCM programs.

**Test Infrastructure:** Uses XCM executor mock framework with:
- `TestBroadcastHandler` - Mock implementation that captures published data in thread-local storage
- `PublishedData` parameter_types - Thread-local `BTreeMap<u32, Vec<([u8;32], Vec<u8>)>>` for verification
- `AllowPublishFrom` - New barrier that only allows `Publish` instruction

**Location:** `polkadot/xcm/xcm-builder/src/tests/publish.rs`

### 2.1 Instruction Execution Tests

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `publish_from_system_parachain_works` | System parachain (ID 1000 < 2000) publishes | Success without registration check |
| `publish_from_non_system_parachain_registered` | Non-system parachain (ID 2000) registered and publishes | Success, data stored |
| `publish_from_non_system_parachain_unregistered` | Non-system parachain (ID 3000) not registered | `Outcome::Incomplete` with `NotRegistered` |
| `publish_from_non_parachain_fails` | Non-parachain origin (Parent) fails | `Outcome::Incomplete` with `BadOrigin` |
| `publish_without_origin_fails` | ClearOrigin before Publish fails | `Outcome::Incomplete` with `BadOrigin` |
| `publish_multiple_items_works` | Multiple key-value pairs in single instruction | All pairs stored in `PublishedData` |
| `publish_from_account_origin_fails` | Account junction origin | `Outcome::Incomplete` with `BadOrigin` |
| `broadcast_handler_error_propagates` | Handler returns storage limit error | `Outcome::Incomplete` with handler's error |

### 2.2 AllowPublishFrom Barrier Tests

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `barrier_allows_system_parachain` | System parachain (ID 1000) with Publish | `should_execute` returns `Ok(())` |
| `barrier_allows_non_system_parachain` | Non-system parachain (ID 2000) with Publish | `should_execute` returns `Ok(())` |
| `barrier_allows_single_publish` | Message with one `Publish` instruction | `should_execute` returns `Ok(())` |
| `barrier_allows_multiple_publish_within_limit` | Message with 3 `Publish` instructions (limit=16) | `should_execute` returns `Ok(())` |
| `barrier_allows_exactly_max_publish` | Message with exactly max (e.g., 4) `Publish` instructions | `should_execute` returns `Ok(())` |
| `barrier_rejects_exceeding_max_publish` | Message with max+1 `Publish` instructions | `should_execute` returns `Err(StackLimitReached)` |
| `barrier_rejects_empty_message` | Empty instruction list | `should_execute` returns `Err(BadFormat)` |
| `barrier_rejects_publish_with_other_instructions` | `Publish` + `DepositAsset` in same message | `should_execute` returns `Err(BadFormat)` |
| `barrier_rejects_other_before_publish` | `ClearOrigin` + `Publish` | `should_execute` returns `Err(BadFormat)` |
| `barrier_rejects_non_publish` | Message with `TransferAsset` only | `should_execute` returns `Err(BadFormat)` |
| `barrier_rejects_non_parachain_origin` | Publish from relay chain origin | `should_execute` returns `Err(Unsupported)` |
| `barrier_filters_specific_parachains` | Filter allows only Parachain(1000) | Only Parachain(1000) passes |

### 2.3 Weight Calculation (Benchmarks)

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `publish_weight_scales_with_data` | Verify weight increases with value size | Weight proportional to data size |
| `publish_weight_scales_with_keys` | Verify weight increases with key count | Weight proportional to key count |

---

## 3. Subscriber Pallet Unit Tests (Parachain)

### 3.1 Subscription Management

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `subscriptions_returns_keys` | SubscriptionHandler returns subscribed keys | Correct keys returned with weight |
| `subscriptions_multiple_publishers` | Subscribe to multiple publishers | All publishers' keys returned |
| `subscriptions_deduplicated` | Same key subscribed multiple times | Deduplicated in processing |
| `subscriptions_combined_by_publisher` | Multiple handlers subscribe to same publisher | Keys combined per publisher |
| `subscriptions_empty_returns_zero_weight` | No subscriptions configured | Empty vec, `Weight::zero()` |
| `subscriptions_multiple_handlers_same_key` | Two handlers subscribe to same (publisher, key) | Key processed only once |

### 3.2 Relay Key Collection

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `relay_keys_includes_subscribed` | relay_keys() returns child trie keys for subscriptions | Correct RelayProofRequest |
| `relay_keys_excludes_disabled` | Disabled publishers excluded from relay_keys | No key for disabled publisher |
| `relay_keys_empty_no_subscriptions` | No subscriptions returns empty request | Empty RelayProofRequest |

### 3.3 Proof Processing - Change Detection

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `unchanged_root_skipped` | Publisher root unchanged from previous block | No processing, no callbacks |
| `changed_root_processed` | Publisher root changed | Keys processed, callbacks invoked |
| `new_publisher_processed` | First time seeing publisher | All keys processed, root cached |
| `multiple_publishers_mixed` | Some publishers changed, some unchanged | Only changed publishers processed |

### 3.4 Proof Processing - Trie Traversal

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `cache_populated_on_first_access` | First proof processing populates cache | CachedTrieNodes contains path nodes |
| `cache_updated_on_change` | Trie structure changes | New nodes added, old nodes removed |
| `unchanged_subtree_skipped` | Node hash matches cached | Skip entire subtree |
| `value_change_detected` | Leaf value changed | `on_data_updated` called |
| `key_not_in_trie` | Subscribed key doesn't exist | No callback, no error |
| `external_data_not_cached` | Value > 32 bytes (external) | Trie node cached, data not cached |
| `value_32_bytes_inlined` | Value exactly 32 bytes | Inlined in trie node (no external fetch) |
| `value_33_bytes_external` | Value exactly 33 bytes | Stored externally (hash reference in node) |
| `cached_node_size_bounded` | Verify BoundedVec<u8, 750> enforced | Nodes stored within size limit |
| `published_entry_decoded_correctly` | Decode PublishedEntry from proof | value, ttl, when_inserted all populated |

### 3.5 Trie Depth Limit

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `depth_within_limit` | Trie depth < MaxTrieDepth | Processing succeeds |
| `depth_exceeds_limit` | Trie depth > MaxTrieDepth | `TrieDepthExceeded` error |
| `depth_exceeded_disables_publisher` | Depth exceeded triggers disable | Publisher added to DisabledPublishers |
| `disabled_publisher_skipped` | Process proof with disabled publisher | Publisher skipped entirely |
| `enable_publisher_removes_disabled` | Call enable_publisher | Publisher removed from DisabledPublishers |
| `depth_limit_bounds_cache` | Verify cache bounded by depth * keys | Cache size <= MaxTrieDepth * num_keys |

### 3.6 TTL State Computation

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `ttl_state_infinite` | Entry with TTL = 0 | `TtlState::Infinite` |
| `ttl_state_valid_for` | Entry with remaining blocks | `TtlState::ValidFor(remaining)` |
| `ttl_state_timed_out` | Entry past expiration | `TtlState::TimedOut` |

### 3.7 Cache Management

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `clear_publisher_cache_removes_nodes` | Call clear_publisher_cache | All CachedTrieNodes for publisher removed |
| `clear_publisher_cache_clears_root` | Clear cache also clears root | PreviousPublishedDataRoots removed |
| `clear_cache_origin_check` | Unauthorized origin tries to clear | Error based on ClearCacheOrigin config |
| `cached_trie_nodes_db_get_existing` | CachedTrieNodesDB::get() for cached hash | Returns cached node bytes |
| `cached_trie_nodes_db_get_missing` | CachedTrieNodesDB::get() for uncached hash | Returns None |

### 3.8 No-op RelayProofExtender

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `noop_extender_relay_keys_empty` | `()` impl returns no keys | Empty `RelayProofRequest` |
| `noop_extender_process_proof_complete` | `()` impl returns Complete | `ProofProcessingResult::Complete` |

---

## 4. Proof Processing & Weight Tracking Tests

### 4.1 Weight Tracking

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `weight_tracks_ref_time` | Verify ref_time consumption | DbWeight::reads(1) per node |
| `weight_tracks_proof_size` | Verify proof_size consumption | Node size added to proof_size |
| `weight_combined_tracking` | Both components tracked together | WeightMeter reflects both |
| `cache_reads_tracked_by_host` | Parachain cache reads | Tracked automatically via host function |
| `relay_proof_reads_manual` | Relay proof reads | Explicitly consumed via meter |

### 4.2 Budget Enforcement

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `budget_exhausted_sets_cursor` | Weight exhausted mid-processing | Cursor set, Incomplete returned |
| `budget_exhausted_mid_key` | Budget runs out during key traversal | Cursor set to current key |
| `budget_exhausted_between_keys` | Budget runs out between keys | Cursor set to next key |
| `budget_exhausted_between_publishers` | Budget runs out between publishers | Cursor set to next publisher |

### 4.3 Weight Limit Respect

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `processing_stops_at_weight_limit` | Given limit of 1000, processing stops before exceeding | `meter.consumed() <= limit` always |
| `processing_stops_before_next_read_exceeds` | Stops when next read would exceed limit | `meter.remaining() < next_read_weight` |
| `small_budget_processes_partial` | Budget allows only 2 of 10 keys | Exactly 2 keys processed, cursor at key 3 |
| `exact_budget_processes_all` | Budget exactly matches required weight | All keys processed, `Complete` returned |
| `zero_budget_processes_nothing` | Budget = 0 | No keys processed, cursor at first key |
| `budget_accounts_for_proof_size` | Large nodes consume more budget | Fewer large nodes fit than small nodes |
| `budget_accounts_for_ref_time` | ref_time component respected | Stops based on ref_time if it's limiting factor |
| `budget_respects_both_dimensions` | Either ref_time or proof_size can be limiting | Stops when either dimension exhausted |
| `consumed_weight_never_exceeds_limit` | Verify invariant across many scenarios | `meter.consumed().all_lte(limit)` always true |
| `meter_state_consistent_after_incomplete` | After Incomplete, meter shows near-limit | `!meter.can_consume(min_weight)` holds |

### 4.3 Cursor Resumption

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `cursor_resumes_at_position` | Next block resumes from cursor | Processing starts at cursor |
| `cursor_wrap_around` | Process remaining then wrap to beginning | Full coverage over multiple blocks |
| `cursor_cleared_on_complete` | All keys processed | Cursor storage cleared |
| `cursor_with_subscription_change` | Subscriptions change between blocks | Cursor adjusted or reset appropriately |

### 4.4 Processing Mode Equivalence

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `prune_verify_same_weight` | Same proof in Prune and Verify modes | Identical WeightMeter consumption |
| `prune_verify_same_cursor` | Same proof, same budget | Same cursor position |
| `prune_no_state_changes` | Prune mode execution | No storage writes |
| `verify_applies_state_changes` | Verify mode execution | Cache updated, roots updated |
| `prune_no_cache_writes` | Prune mode doesn't touch CachedTrieNodes | Storage unchanged |
| `prune_no_root_updates` | Prune mode doesn't touch PreviousPublishedDataRoots | Storage unchanged |
| `prune_no_cursor_writes` | Prune mode doesn't write RelayProofProcessingCursor | Storage unchanged |

### 4.5 Proof Validation

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `all_nodes_accessed_valid` | All proof nodes read during processing | `ensure_no_unused_nodes()` succeeds |
| `extraneous_nodes_invalid` | Proof contains unread nodes | Block validation fails |
| `incomplete_at_limit_valid` | Incomplete with budget exhausted | Valid, cursor set |
| `incomplete_below_limit_invalid` | Incomplete with budget remaining | Block validation fails (collator cheating) |
| `missing_node_at_limit_valid` | Node missing when budget full | Valid (couldn't fit more) |
| `missing_node_below_limit_invalid` | Node missing with budget remaining | Invalid (collator omitted data) |

---

## 5. Priority and Ordering Tests

### 5.1 Publisher Priority

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `system_parachains_first` | Mix of system and public parachains | System parachains (< 2000) processed first |
| `non_system_randomized` | Multiple non-system parachains | Order randomized by block hash |
| `priority_under_budget_constraint` | Limited budget with mixed publishers | System chains more likely to complete |

### 5.2 Key Ordering

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `keys_sorted_within_publisher` | Multiple keys for same publisher | Keys processed in deterministic order |
| `wrap_around_maintains_order` | Cursor wrap-around | Order preserved across wrap |

---

## 6. Integration Tests (BlockTests Framework)

### 6.1 Basic Flow

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `basic_publish_subscribe_flow` | Publisher publishes, subscriber receives | Callback invoked with correct data |
| `multi_block_processing` | Data published, received over multiple blocks | Eventual consistency |
| `subscription_before_publish` | Subscribe before publisher has data | No callback initially, callback when data arrives |

### 6.2 Multi-Publisher Scenarios

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `multiple_publishers_single_subscriber` | Subscribe to 5+ publishers | All publishers' data received |
| `single_publisher_multiple_subscribers` | Multiple parachains subscribe to same publisher | Each receives data independently |
| `overlapping_subscriptions` | Publishers with overlapping key sets | Deduplication works correctly |

### 6.3 Budget Scenarios

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `light_block_large_budget` | Few HRMP messages, large pub-sub budget | All keys processed |
| `heavy_block_small_budget` | Many HRMP messages, small pub-sub budget | Partial processing, cursor set |
| `full_block_no_budget` | Block at 85% limit | Pub-sub gracefully skipped |
| `budget_split_across_blocks` | Large dataset processed over multiple blocks | Eventually all data received |
| `zero_budget_only_static_keys` | DMQ + HRMP consume entire budget | Proof contains only static relay keys, no pub-sub child trie data |
| `budget_after_dmq_hrmp_correct` | Verify remaining budget after message filtering | `size_limit` reflects actual remaining space |

### 6.4 Cache Behavior

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `cache_reduces_proof_size` | Subsequent blocks need smaller proofs | Proof size decreases |
| `cache_survives_no_changes` | Publisher unchanged for many blocks | Cache persists, no proof needed |
| `subscription_removal_and_cache_clear` | Remove subscription, clear cache | Cache cleared, subsequent proof full size |

### 6.5 Error Recovery

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `publisher_disabled_then_enabled` | Depth exceeded, then re-enabled | Resumes processing after enable |
| `cursor_recovery_after_restart` | Node restart with cursor set | Resumes from cursor |

---

## 7. Malicious/Adversarial Tests

### 7.1 Malicious Collator Detection

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `collator_omits_data_below_limit` | Proof missing nodes with budget remaining | Block rejected |
| `collator_includes_extraneous_data` | Proof contains unrequested nodes | Block rejected |
| `collator_wrong_cursor` | Cursor doesn't match proof contents | Block rejected |
| `collator_inflated_proof` | Proof larger than necessary | Block rejected (extraneous nodes) |

### 7.2 Malicious Publisher

| Test Case | Description | Expected Outcome |
|-----------|-------------|------------------|
| `publisher_pathological_trie` | Publisher creates very deep trie | Publisher disabled, other publishers unaffected |
| `publisher_rapid_changes` | Publisher changes data every block | Subscriber keeps up or cursor manages backlog |

---

## 8. Zombienet End-to-End Tests

### 8.1 Basic Functionality

| Test Case | Description | Setup |
|-----------|-------------|-------|
| `e2e_publish_subscribe` | Basic pub-sub flow | 2 validators, 1 publisher parachain, 1 subscriber parachain |
| `e2e_ttl_expiration` | Data expires after TTL | Publisher with finite TTL, verify deletion on relay |
| `e2e_system_parachain_publisher` | System parachain publishes | Asset Hub as publisher, Penpal as subscriber |

### 8.2 Performance & Load

| Test Case | Description | Setup |
|-----------|-------------|-------|
| `e2e_budget_under_hrmp_load` | Pub-sub with HRMP traffic | Publisher + subscriber + HRMP sender/receiver |
| `e2e_large_dataset` | Large number of keys | Publisher with 1000+ keys, verify eventual delivery |
| `e2e_multiple_publishers` | Many-to-one subscription | 5 publishers, 1 subscriber |

### 8.3 Recovery Scenarios

| Test Case | Description | Setup |
|-----------|-------------|-------|
| `e2e_collator_restart` | Subscriber collator restarts | Verify cursor recovery |
| `e2e_validator_restart` | Relay validator restarts | Verify no data loss |

---

## 9. Benchmark Tests

### 9.1 Broadcaster Pallet

- `bench_register_publisher` - Registration with deposit
- `bench_deregister_publisher` - Deregistration with cleanup
- `bench_publish` - Single key publish
- `bench_publish_update` - Update existing key
- `bench_delete_keys` - Manual key deletion
- `bench_on_idle_cleanup` - TTL cleanup per key

### 9.2 XCM Instruction

- `bench_publish_instruction` - Publish instruction weight

### 9.3 Subscriber Pallet

- `bench_process_proof_single_key` - Single key processing
- `bench_process_proof_cached` - Processing with full cache
- `bench_process_proof_no_cache` - Processing without cache
- `bench_clear_publisher_cache` - Cache clearing

---

## 10. Edge Cases Checklist

### 10.1 Boundary Conditions

- [ ] Key exactly 32 bytes
- [ ] Value exactly `MaxValueLength` bytes
- [ ] Value exactly 32 bytes (inline threshold)
- [ ] Value exactly 33 bytes (just above inline)
- [ ] TTL = 0 (infinite)
- [ ] TTL = 1 (minimum finite)
- [ ] TTL = u32::MAX (maximum finite)
- [ ] Exactly `MaxStoredKeys` keys
- [ ] Exactly `MaxPublishers` publishers
- [ ] Exactly `MaxTrieDepth` traversal depth
- [ ] Weight budget exactly sufficient for one more key
- [ ] Weight budget exactly zero remaining
- [ ] Trie node exactly 750 bytes (max cached size)
- [ ] Subscription to publisher with exactly 1 key
- [ ] Proof with exactly 1 node (root only)

### 10.2 Empty/Null Conditions

- [ ] No subscriptions
- [ ] No publishers registered
- [ ] Empty child trie (no keys)
- [ ] Subscription to non-existent publisher
- [ ] Proof with only root node
- [ ] Cache completely empty

### 10.3 State Transitions

- [ ] First block after subscription added
- [ ] First block after subscription removed
- [ ] First block after publisher registered
- [ ] First block after publisher deregistered
- [ ] Transition from no cursor to cursor
- [ ] Transition from cursor to no cursor
- [ ] Publisher transitions: enabled → disabled → enabled

### 10.4 Concurrent Operations

- [ ] Publish while being subscribed to
- [ ] Deregister while subscribers active
- [ ] Clear cache while proof processing
- [ ] TTL expiry during proof processing block

### 10.5 Version/Upgrade Scenarios

- [ ] Runtime upgrade with active subscriptions
- [ ] Runtime upgrade with cursor set
- [ ] Runtime upgrade with cached data
