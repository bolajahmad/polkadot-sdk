# Tasks: Add Pub-Sub System

## 1. Broadcaster Pallet (Relay Chain)

- [x] 1.1 Create `polkadot/runtime/parachains/src/broadcaster/mod.rs` with pallet boilerplate
- [x] 1.2 Implement `Config` trait with storage limits and deposit configuration:
  - `MaxValueLength`, `MaxStoredKeys`, `MaxTotalStorageSize`, `MaxPublishers`, `PublisherDeposit`
- [x] 1.3 Add `Publishers` storage map for registration tracking
- [x] 1.4 Implement `register_publisher` extrinsic with deposit handling for public parachains
- [x] 1.5 Implement `force_register_publisher` for system parachains (Root only, zero deposit)
- [x] 1.6 Allow system parachains (ID < 2000) to publish without registration
  - **Design Decision**: System parachains use `force_register_publisher` with zero deposit instead of bypassing registration entirely. This provides explicit governance control and consistent registration tracking.
- [x] 1.7 Implement `deregister_publisher` extrinsic with deposit release
- [x] 1.8 Implement `force_deregister_publisher` extrinsic for governance
- [x] 1.9 Add child trie storage using `derive_child_info(para_id)`:
  - Key format: `(b"pubsub", para_id).encode()`
- [x] 1.10 Define `PublishedEntry<BlockNumber>` struct with (value, ttl, when_inserted)
- [x] 1.11 Implement `handle_publish` for XCM executor integration
- [x] 1.12 Add storage limit enforcement (keys, value size, total size)
- [x] 1.13 Add `TtlData` storage: `StorageDoubleMap<ParaId, [u8; 32], (u32, BlockNumber)>`
- [x] 1.14 Add `TtlScanCursor` storage: `StorageValue<(ParaId, [u8; 32])>`

- [x] 1.16 Implement `on_idle` TTL cleanup:
  - Scan `TtlData` for expired keys
  - Delete up to `MaxTtlScansPerIdle` (500) keys per block
  - Use `TtlScanCursor` for resumption
- [x] 1.17 Implement `delete_keys` extrinsic for parachain self-deletion
- [x] 1.18 Implement `force_delete_keys` extrinsic for governance
- [x] 1.19 Add events: `PublisherRegistered`, `PublisherDeregistered`, `DataPublished`, `KeyExpired`, `KeysDeleted`, `KeysForcedDeleted`
- [x] 1.20 Implement cleanup on parachain offboarding hook
- [x] 1.21 Write unit tests for registration/deregistration and system parachain bypass
- [x] 1.22 Write unit tests for publish operations and limits
- [x] 1.23 Write unit tests for TTL logic (infinite, finite, capped, reset, finite→infinite, infinite→finite)
- [x] 1.24 Write unit tests for manual deletion (removes TtlData metadata)
- [x] 1.25 Add benchmarks for all extrinsics

## 2. XCM Publish Instruction

- [x] 2.1 Add `Publish { data: PublishData }` to `polkadot/xcm/src/v5/instruction.rs`
- [x] 2.2 Add `PublishData` type (bounded vec of key-value pairs)
- [x] 2.3 Add `MaxPublishValueLength` and `MaxPublishKeys` parameter types
- [x] 2.4 Implement `Publish` instruction handler in XCM executor
- [x] 2.5 Add origin validation (must be Parachain junction)
- [x] 2.6 Integrate with broadcaster pallet via `Config::BroadcastHandler` trait
- [x] 2.7 Add `AllowPublishFrom<T, MaxPublishInstructions>` barrier in `xcm-builder/src/barriers.rs`:
  - Only allows messages containing just `Publish` instructions
  - `MaxPublishInstructions: Get<u32>` - configurable limit on number of Publish instructions per message
  - Similar pattern to `AllowSubscriptionsFrom`
  - Enables free execution for Publish without opening up all instructions
  - Returns `StackLimitReached` if instruction count exceeds max
- [x] 2.8 Write unit tests for XCM instruction execution
- [x] 2.9 Write unit tests for `AllowPublishFrom` barrier
- [x] 2.10 Add benchmarks for `Publish` instruction weight

## 3. Subscriber Pallet (Parachains)

- [x] 3.1 Create `cumulus/pallets/subscriber/src/lib.rs` with pallet boilerplate
- [x] 3.2 Add `MaxTrieDepth` config parameter to limit trie traversal depth
- [x] 3.3 Add `DisabledPublishers` storage: `StorageMap<ParaId, DisableReason>`
- [x] 3.4 Implement `enable_publisher(ParaId)` extrinsic for re-enabling disabled publishers
- [x] 3.5 Add events: `PublisherDisabled`, `PublisherEnabled`
- [x] 3.6 Define `SubscribedKey` type with H256 wrapper and methods:
  - `from_hash([u8; 32])` for pre-computed hashes
  - `from_data(&[u8])` for runtime hashing
- [x] 3.7 Implement `subscribed_key!` macro for compile-time hashing via `sp_crypto_hashing::blake2_256`
- [x] 3.8 Define `TtlState` enum (Infinite, ValidFor(u32), TimedOut)
- [x] 3.9 Define `PublishedEntry<BlockNumber>` struct with (value, ttl, when_inserted)
- [x] 3.10 Define `SubscriptionHandler` trait:
  - `subscriptions() -> (Vec<(ParaId, Vec<SubscribedKey>)>, Weight)`
  - `on_data_updated(ParaId, SubscribedKey, &[u8], TtlState) -> Weight`
- [x] 3.11 Implement `clear_publisher_cache(origin, ParaId)` dispatchable for cache cleanup after subscription removal
- [x] 3.11 Add `PreviousPublishedDataRoots` storage for change detection
- [x] 3.12 Add `CachedTrieNodes` storage: `StorageDoubleMap<ParaId, H256, BoundedVec<u8, 512>>` (trie nodes only, no external data)
- [x] 3.13 Add `RelayProofProcessingCursor` storage: `StorageValue<(ParaId, SubscribedKey)>`
- [x] 3.14 Implement `compute_ttl_state()` to convert PublishedEntry to TtlState
- [x] 3.15 Implement publisher prioritization (system parachains first)
- [x] 3.16 Write unit tests for subscription handling
- [x] 3.17 Write unit tests for trie depth limit enforcement and publisher disabling
- [x] 3.18 Write unit tests for enable_publisher re-enabling
- [x] 3.19 Add benchmarks for proof processing

## 4. Proof Collection (Collator)

- [x] 4.1 Add `RelayProofExtender` trait to `cumulus/pallets/parachain-system/src/lib.rs`:
  - `fn relay_keys() -> RelayProofRequest`
  - `fn process_proof(...) -> ProofProcessingResult`
  - No-op impl for `()`
- [x] 4.2 Add `RelayProofExtender` as Config parameter in parachain-system pallet (default `()`)
- [x] 4.3 Add `ParachainSystem::relay_keys_to_prove()` helper that calls `T::RelayProofExtender::relay_keys()`
- [x] 4.4 Document runtime integration: implement `KeyToIncludeInRelayProof` calling `ParachainSystem::relay_keys_to_prove()`
- [x] 4.5 Add example implementation to test parachain (Penpal)
- [x] 4.6 Write unit tests for proof collection

## 5. RelayProofExtender, WeightMeter, and AccessedNodesTracker

- [x] 5.1 Use `WeightMeter` from `sp_weights` for weight tracking:
  - Tracks both `ref_time` (computation) and `proof_size` (storage)
  - Parachain storage reads tracked automatically via host function + `StorageWeightReclaimer`
  - Relay proof reads: consume `T::DbWeight::get().reads(1) + Weight::from_parts(0, node_size)`
  - Use `meter.try_consume()` for safe consumption, `meter.can_consume()` for checks
- [x] 5.2 Use `AccessedNodesTracker` from `sp_trie::accessed_nodes_tracker`:
  - Implements `TrieRecorder` for automatic node access tracking
  - Use with `TrieDBBuilder::with_recorder()` for trie operations
  - `ensure_no_unused_nodes()` validates all proof nodes were read
- [x] 5.3 Define `ProcessingMode` enum: `Prune` (off-chain), `Verify` (on-chain)
- [x] 5.4 Define `RelayProofExtender` trait:
  - `extra_keys() -> Vec<RelayStorageKey>` (returns keys to include in proof)
  - `process_proof(&MemoryDB, H256, &mut AccessedNodesTracker, &mut WeightMeter, ProcessingMode) -> ProofProcessingResult`
- [x] 5.5 Implement `RelayProofExtender` for pub-sub pallet:
  - `extra_keys()`: Return child trie keys for subscribed publishers
  - `process_proof()`: Unified logic for Prune/Verify modes
- [x] 5.6 Implement proof processing logic with WeightMeter:
  - Detect unchanged child tries via `PreviousPublishedDataRoots` comparison
  - Skip unchanged child tries entirely (no reads needed)
  - Consume weight for each relay proof node read: `ref_time` + `proof_size`
  - Parachain proof (cache reads) tracked automatically via host function
  - Stop when `!meter.can_consume(next_weight)` and set cursor
  - Priority ordering: system chains first, then randomized for others
- [x] 5.7 Implement dual-trie traversal:
  - Old trie via `CachedTrieNodesDB` (cache reads tracked by host function)
  - New trie via proof `MemoryDB` with `AccessedNodesTracker` recorder
  - Add new nodes to cache (Verify mode only)
  - Remove outdated nodes from cache (Verify mode only)
  - Stop at unchanged nodes (subtree same)
  - Abort if depth exceeds `MaxTrieDepth`
- [x] 5.8 Implement `clear_publisher_cache(ParaId)` dispatchable for subscription removal
- [x] 5.9 Integrate in `provide_inherent` (collator, off-chain):
  - Call `process_proof()` with `ProcessingMode::Prune`
  - WeightMeter simulates cache reads that will happen on-chain
  - Removes unprocessed data from proof after weight exhausted
- [x] 5.10 Integrate in `set_validation_data` (on-chain):
  - Create `WeightMeter::with_limit(weight_limit)`
  - Create `AccessedNodesTracker::new(proof.len())`
  - Process static keys automatically
  - Call `process_proof()` with `ProcessingMode::Verify`
  - Call `tracker.ensure_no_unused_nodes()` to validate no extraneous data
  - If result is `Incomplete`, verify `!meter.can_consume(min_weight)` (weight exhausted)
  - Panic if proof invalid
- [x] 5.11 Write unit tests for weight tracking (ref_time + proof_size)
- [x] 5.12 Write unit tests for `AccessedNodesTracker` access tracking
- [x] 5.13 Write unit tests for proof processing (unchanged tries, cached nodes)
- [x] 5.14 Write unit tests for budget enforcement with combined proof+cache usage
- [x] 5.15 Write unit tests for trie depth limit enforcement
- [x] 5.16 Write unit tests for light block (large pub-sub budget)
- [x] 5.17 Write unit tests for heavy block (small pub-sub budget)
- [x] 5.18 Write unit tests for full block (no pub-sub budget, graceful skip)
- [x] 5.19 Write unit tests for proof validation (all nodes accessed, missing at limit only)
- [x] 5.20 Write unit tests for invalid proof detection (missing below limit, extraneous nodes)
- [x] 5.21 Write unit tests verifying Prune and Verify modes produce same WeightMeter results

## 6. Integration and Testing

See `test-plan.md` for comprehensive test plan with all edge cases.

### 6.1 Runtime Integration
- [x] 6.1.1 Add broadcaster pallet to relay chain runtime
- [x] 6.1.2 Add subscriber pallet to test parachain runtime (Penpal)
- [x] 6.1.3 Implement example `SubscriptionHandler` in test parachain
- [x] 6.1.4 Configure `KeyToIncludeInRelayProof` runtime API in test parachain

### 6.2 Integration Tests (BlockTests Framework)
- [x] 6.2.1 Basic publish-subscribe flow (single publisher, single subscriber)
- [x] 6.2.2 Multiple publishers, single subscriber
- [x] 6.2.3 Single publisher, multiple keys
- [x] 6.2.4 Unchanged publisher root skipped (no callbacks)
- [x] 6.2.5 Cache populated on first access
- [x] 6.2.6 Cache updated on trie structure change
- [x] 6.2.7 Unchanged subtree skipped (matching node hash)
- [x] 6.2.8 PoV budget exhausted mid-processing (cursor set)
- [x] 6.2.9 Cursor resumption with wrap-around
- [x] 6.2.10 Light block (large pub-sub budget) - `process_proof_large_budget_processes_all_keys`
- [x] 6.2.11 Heavy block (small pub-sub budget from HRMP) - `process_proof_tiny_budget_returns_incomplete_immediately`
- [x] 6.2.12 Full block (no pub-sub budget, graceful skip) - `process_proof_zero_budget_graceful_skip`
- [x] 6.2.13 TTL expiration and cleanup
- [x] 6.2.14 Subscription removal and cache clearing

### 6.3 Proof Validation Tests
- [x] 6.3.1 All proof nodes accessed - valid - `all_proof_nodes_accessed_complete_processing`
- [x] 6.3.2 Extraneous nodes in proof - invalid (validated by AccessedNodesTracker at parachain-system level)
- [x] 6.3.3 Incomplete at budget limit - valid - `incomplete_at_budget_limit_sets_cursor`
- [x] 6.3.4 Incomplete below budget limit - invalid (validated by parachain-system via ensure_no_unused_nodes)
- [x] 6.3.5 Prune and Verify modes produce same weight consumption - `process_proof_prune_and_verify_consume_similar_weight`

### 6.4 Edge Case Tests
- [x] 6.4.1 Trie depth exceeds MaxTrieDepth (publisher disabled)
- [x] 6.4.2 Re-enable disabled publisher
- [x] 6.4.3 System parachain priority in processing order
- [x] 6.4.4 Boundary: value exactly 32 bytes (inline threshold) - `value_exactly_32_bytes_inline_storage`
- [x] 6.4.5 Boundary: value exactly 33 bytes (external storage) - `value_exactly_33_bytes_external_storage`
- [x] 6.4.6 Empty child trie (publisher has no data) - `empty_child_trie_no_data`
- [x] 6.4.7 Subscription to non-existent publisher - `subscription_to_non_existent_publisher`

### 6.5 Zombienet End-to-End Tests
- [x] 6.5.1 Basic: 2 relay validators + publisher parachain + subscriber parachain (covered by emulated tests)
- [x] 6.5.2 TTL expiration observed from subscriber (`ttl_expiration_scenario`)
- [x] 6.5.3 PoV budget under HRMP load (unit tests cover budget scenarios)
- [x] 6.5.4 Multiple publishers (5+) with single subscriber (unit test: `process_proof_multiple_publishers_partial_processing`)
- [x] 6.5.5 Large dataset (1000+ keys) eventual delivery (cursor resumption tests cover this pattern)
- [x] 6.5.6 Collator restart with cursor recovery (`process_proof_cursor_resumes_from_correct_position`)

## 7. Documentation

- [x] 7.1 Write user guide for publishers (key hashing, XCM usage, TTL examples)
- [x] 7.2 Write user guide for subscribers (trait implementation, caching, TTL handling)
- [x] 7.3 Add inline rustdoc for all public types and traits
- [x] 7.4 Update CHANGELOG with new feature entry
