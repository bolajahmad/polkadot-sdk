# Pub-Sub System Specification

Cross-chain publish-subscribe mechanism for data sharing via the relay chain.

## ADDED Requirements

### Requirement: Publisher Registration

The broadcaster pallet SHALL allow parachains to register as publishers with a deposit.

#### Scenario: Public parachain registration

- **GIVEN** a parachain with ID 2000 that is not registered
- **WHEN** an account calls `register_publisher(para_id: 2000)` with sufficient balance
- **THEN** the deposit is held from the caller's account
- **AND** the parachain is registered as a publisher
- **AND** a `PublisherRegistered` event is emitted

#### Scenario: System parachain publishes without registration

- **GIVEN** a system parachain with ID 1000 (< 2000)
- **WHEN** the parachain sends a `Publish` instruction
- **THEN** the publish operation succeeds without requiring registration
- **AND** data is stored in the parachain's child trie

#### Scenario: Registration fails when already registered

- **GIVEN** parachain 2000 is already registered
- **WHEN** `register_publisher(para_id: 2000)` is called
- **THEN** the call fails with `AlreadyRegistered` error

#### Scenario: Registration fails when max publishers reached

- **GIVEN** the number of registered publishers equals `MaxPublishers`
- **WHEN** a new registration is attempted
- **THEN** the call fails with `TooManyPublishers` error

### Requirement: Publisher Deregistration

The broadcaster pallet SHALL allow publishers to deregister and reclaim deposits.

#### Scenario: Voluntary deregistration

- **GIVEN** parachain 2000 is registered with a deposit
- **WHEN** the manager calls `deregister_publisher(para_id: 2000)`
- **THEN** all published data is deleted from the child trie
- **AND** the deposit is released to the manager
- **AND** a `PublisherDeregistered` event is emitted

#### Scenario: Force deregistration by governance

- **GIVEN** parachain 2000 is registered
- **WHEN** root calls `force_deregister_publisher(para_id: 2000)`
- **THEN** all published data is deleted
- **AND** the deposit is slashed or returned based on configuration
- **AND** a `PublisherDeregistered` event is emitted

### Requirement: XCM Publish Instruction

The XCM executor SHALL support a `Publish` instruction for storing key-value data on the relay chain. Keys MUST be 32-byte values (publishers hash their keys before publishing).

#### Scenario: Successful publish

- **GIVEN** parachain 2000 is registered as a publisher
- **WHEN** the parachain sends XCM containing `Publish { key: [0u8; 32], value: vec![1, 2, 3], ttl: 0 }`
- **THEN** the key is stored directly as the 32-byte value (no additional hashing)
- **AND** the value is stored in the parachain's child trie
- **AND** a `DataPublished` event is emitted

#### Scenario: Publish with finite TTL

- **GIVEN** parachain 2000 is registered
- **WHEN** the parachain sends `Publish { key, value, ttl: 1000 }`
- **THEN** the entry is stored with expiration at `current_block + 1000`
- **AND** TTL metadata is recorded for cleanup scheduling

#### Scenario: Publish fails for unregistered public parachain

- **GIVEN** public parachain 3000 (>= 2000) is not registered
- **WHEN** the parachain sends a `Publish` instruction
- **THEN** the instruction fails with `NotRegistered` error

#### Scenario: Publish fails when storage limit exceeded

- **GIVEN** parachain 2000 has used its `MaxTotalStorageSize` quota
- **WHEN** the parachain sends a `Publish` instruction
- **THEN** the instruction fails with `TotalStorageSizeExceeded`

### Requirement: AllowPublishFrom Barrier

The XCM barrier `AllowPublishFrom<T, MaxPublishInstructions>` SHALL allow free execution of messages containing only `Publish` instructions from allowed origins, up to a configurable maximum count.

#### Scenario: Barrier allows single Publish instruction

- **GIVEN** `AllowPublishFrom<Everything, ConstU32<16>>` is configured as a barrier
- **AND** parachain 2000 sends XCM containing only `Publish { data }`
- **WHEN** the barrier evaluates the message
- **THEN** execution is allowed without requiring fee payment

#### Scenario: Barrier allows multiple Publish instructions within limit

- **GIVEN** `AllowPublishFrom<Everything, ConstU32<16>>` is configured as a barrier
- **AND** parachain 2000 sends XCM containing `[Publish { data1 }, Publish { data2 }, Publish { data3 }]`
- **WHEN** the barrier evaluates the message
- **THEN** execution is allowed without requiring fee payment
- **AND** all three Publish instructions are executed

#### Scenario: Barrier rejects too many Publish instructions

- **GIVEN** `AllowPublishFrom<Everything, ConstU32<4>>` is configured with max 4 instructions
- **AND** parachain 2000 sends XCM containing 5 `Publish` instructions
- **WHEN** the barrier evaluates the message
- **THEN** the barrier rejects with `StackLimitReached` error

#### Scenario: Barrier allows exactly max Publish instructions

- **GIVEN** `AllowPublishFrom<Everything, ConstU32<4>>` is configured with max 4 instructions
- **AND** parachain 2000 sends XCM containing exactly 4 `Publish` instructions
- **WHEN** the barrier evaluates the message
- **THEN** execution is allowed without requiring fee payment

#### Scenario: Barrier rejects Publish mixed with other instructions

- **GIVEN** `AllowPublishFrom<Everything, ConstU32<16>>` is configured as a barrier
- **AND** parachain 2000 sends XCM containing `Publish { data }` followed by `DepositAsset`
- **WHEN** the barrier evaluates the message
- **THEN** the barrier rejects with `BadFormat` error
- **AND** the message requires a different barrier (e.g., `AllowTopLevelPaidExecutionFrom`)

#### Scenario: Barrier rejects non-Publish messages

- **GIVEN** `AllowPublishFrom<Everything, ConstU32<16>>` is configured as a barrier
- **AND** parachain 2000 sends XCM containing only `TransferAsset`
- **WHEN** the barrier evaluates the message
- **THEN** the barrier rejects with `BadFormat` error

#### Scenario: Barrier filters by origin

- **GIVEN** `AllowPublishFrom<Equals<Parachain(1000)>, ConstU32<16>>` is configured
- **AND** parachain 2000 sends XCM containing only `Publish { data }`
- **WHEN** the barrier evaluates the message
- **THEN** the barrier rejects with `Unsupported` error (origin not in filter)

#### Scenario: Barrier combined with other barriers

- **GIVEN** barrier chain: `AllowPublishFrom<Everything, ConstU32<16>>`, `AllowTopLevelPaidExecutionFrom<Everything>`
- **AND** parachain 2000 sends XCM containing only `Publish { data }`
- **WHEN** the barrier chain evaluates the message
- **THEN** `AllowPublishFrom` matches and allows free execution
- **AND** subsequent barriers are not evaluated

### Requirement: Data Storage Limits

The broadcaster pallet SHALL enforce per-publisher storage limits.

#### Scenario: Key count limit

- **GIVEN** a publisher has `MaxStoredKeys` keys stored
- **WHEN** the publisher attempts to store a new key
- **THEN** the operation fails with `TooManyKeys` error

#### Scenario: Value size limit

- **GIVEN** `MaxValueLength` is 2048 bytes
- **WHEN** a publisher attempts to store a value larger than 2048 bytes
- **THEN** the operation fails with `ValueTooLarge` error

#### Scenario: Total storage size limit

- **GIVEN** a publisher's total storage usage equals `MaxTotalStorageSize`
- **WHEN** the publisher attempts to store additional data
- **THEN** the operation fails with `TotalStorageSizeExceeded` error

### Requirement: Subscription Handler

The subscriber pallet SHALL provide a trait for declaring subscriptions and receiving updates. Data is received as `PublishedEntry` containing value, TTL, and insertion block number.

#### Scenario: Subscription declaration

- **GIVEN** a parachain implements `SubscriptionHandler`
- **WHEN** `subscriptions()` is called
- **THEN** it returns a tuple of (Vec<(ParaId, Vec<SubscribedKey>)>, Weight)
- **AND** each `SubscribedKey` wraps an H256 hash
- **AND** the Weight represents the cost of computing subscriptions

#### Scenario: Adding subscriptions

- **GIVEN** a parachain subscribes to new keys
- **WHEN** `subscriptions()` includes the new keys
- **THEN** the subscriber pallet automatically fetches and caches data for new keys
- **AND** `on_data_updated` is called when data is received

#### Scenario: Removing subscriptions requires cache clear

- **GIVEN** a parachain removes a subscription to publisher 1000
- **WHEN** the subscription is removed from `subscriptions()` return value
- **THEN** stale cached nodes remain in storage (not automatically cleaned)
- **AND** an authorized origin MUST call `clear_publisher_cache(1000)` to free storage
- **AND** subsequent blocks will rebuild the cache with current subscriptions only

#### Scenario: Data update callback

- **GIVEN** a subscription exists for publisher 1000, key K
- **WHEN** publisher 1000 updates key K and a new block is produced
- **THEN** `on_data_updated(1000, K, value, ttl_state)` is called on the subscriber
- **AND** `value` is the raw published bytes
- **AND** `ttl_state` is one of: `Infinite`, `ValidFor(remaining_blocks)`, or `TimedOut`

#### Scenario: Compile-time key hashing

- **GIVEN** a developer uses `subscribed_key!("my_key")`
- **THEN** the Blake2-256 hash is computed at compile time via `sp_crypto_hashing::blake2_256`
- **AND** runtime hashing overhead is zero
- **AND** the result is a `SubscribedKey` wrapping an H256

#### Scenario: Runtime key hashing

- **GIVEN** a developer uses `SubscribedKey::from_data(dynamic_bytes)`
- **THEN** the Blake2-256 hash is computed at runtime
- **AND** the resulting `SubscribedKey` can be used in subscriptions

#### Scenario: Pre-computed hash

- **GIVEN** a developer has a pre-computed 32-byte hash
- **WHEN** they use `SubscribedKey::from_hash(hash_bytes)`
- **THEN** the hash is used directly without additional hashing

### Requirement: Change Detection

The `RelayProofExtender` SHALL skip processing unchanged publishers using root comparison against `PreviousPublishedDataRoots`.

#### Scenario: Root unchanged

- **GIVEN** publisher 1000's child trie root is cached in `PreviousPublishedDataRoots` as R
- **WHEN** `RelayProofExtender::process_proof()` processes a new block with the same root R
- **THEN** the child trie is skipped entirely (no proof/cache reads needed)
- **AND** `on_data_updated` is NOT called for any keys from publisher 1000

#### Scenario: Root changed

- **GIVEN** publisher 1000's cached root in `PreviousPublishedDataRoots` is R1
- **WHEN** `RelayProofExtender::process_proof()` processes a new block with root R2 (different from R1)
- **THEN** subscribed keys are extracted and processed
- **AND** `on_data_updated` is called for each subscribed key with data
- **AND** `PreviousPublishedDataRoots` is updated with R2

### Requirement: Trie Depth Limit

The subscriber pallet SHALL enforce a maximum trie depth (`MaxTrieDepth`) when processing proofs. Tries deeper than this limit are not supported. When exceeded, the entire publisher is disabled.

#### Scenario: Proof within depth limit

- **GIVEN** `MaxTrieDepth` is configured (e.g., 8)
- **AND** a proof path has depth 6
- **WHEN** the proof is processed
- **THEN** processing succeeds normally

#### Scenario: Proof exceeds depth limit

- **GIVEN** `MaxTrieDepth` is configured (e.g., 8)
- **AND** publisher 1000 has a proof path with depth 10
- **WHEN** the proof is processed
- **THEN** processing fails with `TrieDepthExceeded` error
- **AND** the entire publisher 1000 is skipped (all keys)
- **AND** publisher 1000 is added to `DisabledPublishers` storage
- **AND** a `PublisherDisabled` event is emitted with reason `TrieDepthExceeded`

#### Scenario: Disabled publisher is skipped

- **GIVEN** publisher 1000 is in `DisabledPublishers` storage
- **WHEN** `RelayProofExtender::relay_keys()` is called (via `ParachainSystem::relay_keys_to_prove()`)
- **THEN** publisher 1000's child trie is excluded from the key list
- **AND** no proof data is collected for publisher 1000

#### Scenario: Re-enable disabled publisher

- **GIVEN** publisher 1000 is in `DisabledPublishers` storage
- **WHEN** governance or authorized origin calls `enable_publisher(1000)`
- **THEN** publisher 1000 is removed from `DisabledPublishers`
- **AND** a `PublisherEnabled` event is emitted
- **AND** next block will attempt to process publisher 1000 again

#### Scenario: Depth limit bounds cache size

- **GIVEN** `MaxTrieDepth` is 8
- **AND** a subscriber has 100 subscribed keys
- **WHEN** calculating maximum cache size
- **THEN** maximum nodes per key path is bounded by `MaxTrieDepth`
- **AND** total cache is bounded by `num_keys * MaxTrieDepth` nodes

### Requirement: Trie Node Caching

The subscriber pallet SHALL cache trie nodes (structure only, not data) needed to access subscribed keys, up to `MaxTrieDepth`. Caching uses a `CachedTrieNodes` storage map keyed by (ParaId, H256 node hash). With V1 trie format, data larger than 32 bytes is stored externally and not included in the cache.

#### Scenario: Initial proof processing

- **GIVEN** a new subscription to publisher 1000 with 100 keys
- **WHEN** the first proof is processed
- **THEN** all trie nodes in the proof paths to subscribed keys are cached on-chain
- **AND** nodes are stored in `CachedTrieNodes` storage
- **AND** traversal stops if depth exceeds `MaxTrieDepth`

#### Scenario: Subsequent proof with cached nodes

- **GIVEN** nodes for publisher 1000 are cached
- **WHEN** a new block's proof is built via `provide_inherent`
- **THEN** cached nodes are pruned from the relay chain proof
- **AND** nodes leading to unsubscribed keys are pruned from the proof
- **AND** only new/changed nodes for subscribed keys are included

#### Scenario: Cache synchronization via dual-trie traversal

- **GIVEN** publisher 1000's child trie root has changed
- **WHEN** proof processing traverses the new trie
- **THEN** new nodes not in cache are added to `CachedTrieNodes`
- **AND** cached nodes not in new trie are removed from cache
- **AND** traversal stops at unchanged nodes (entire subtree same)

#### Scenario: Subscription change clears cache

- **GIVEN** subscription to publisher 1000 changes from keys [A, B] to [C, D]
- **WHEN** subscription change is detected
- **THEN** `clear_cache_for_publisher(1000)` is called
- **AND** all cached nodes for publisher 1000 are removed
- **AND** next block includes full proof for new subscribed keys

#### Scenario: Partial subscription caching

- **GIVEN** publisher 1000 has keys [A, B, C, D, E]
- **AND** subscriber only subscribes to keys [A, B]
- **WHEN** proof is processed
- **THEN** cache contains only nodes for paths to [A, B]
- **AND** nodes for paths to [C, D, E] are NOT cached

### Requirement: PoV Budget Constraint

The subscriber pallet SHALL respect PoV budget limits during proof processing. PoV budget includes BOTH proof data AND cache reads. A `WeightMeter` tracks combined usage to ensure the same logic runs off-chain (pruning in `provide_inherent`) and on-chain (verification in `set_validation_data`).

#### Scenario: Budget calculation

- **GIVEN** `allowed_pov_size = validation_data.max_pov_size * 85%`
- **AND** messages have been filtered via `into_abridged(&mut size_limit)`
- **WHEN** pub-sub proof processing begins
- **THEN** pub-sub uses the remaining `size_limit` after message filtering
- **AND** no minimum budget is guaranteed (pub-sub gets what's left)

#### Scenario: Light block with large pub-sub budget

- **GIVEN** a block with few HRMP messages (500 KB PoV)
- **AND** allowed PoV is 4.25 MB (85% of 5 MB)
- **WHEN** pub-sub budget is calculated
- **THEN** approximately 3.75 MB is available for pub-sub

#### Scenario: Heavy block with small pub-sub budget

- **GIVEN** a block with many HRMP messages (4 MB PoV)
- **AND** allowed PoV is 4.25 MB
- **WHEN** pub-sub budget is calculated
- **THEN** approximately 250 KB is available for pub-sub

#### Scenario: Full block with no pub-sub budget

- **GIVEN** a block that uses the full 85% PoV limit
- **WHEN** pub-sub budget is calculated
- **THEN** 0 bytes are available for pub-sub
- **AND** pub-sub gracefully skips this block and retries next block

#### Scenario: WeightMeter tracks ref_time and proof_size

- **GIVEN** a `WeightMeter` with weight limit
- **WHEN** processing reads from parachain storage (cache) AND relay proof nodes
- **THEN** parachain storage reads are tracked automatically via host function + `StorageWeightReclaimer`
- **AND** relay proof reads consume weight: `T::DbWeight::get().reads(1) + Weight::from_parts(0, node_size)`
- **AND** `meter.remaining()` reflects available weight for both `ref_time` and `proof_size`
- **AND** the same meter behavior occurs in both off-chain (Prune) and on-chain (Verify) modes

#### Scenario: Weight exhausted mid-processing

- **GIVEN** available weight budget and operations exceeding it
- **WHEN** `!meter.can_consume(next_weight)` returns true
- **THEN** processing stops at current key
- **AND** remaining nodes are removed from the proof (off-chain) or not accessed (on-chain)
- **AND** `RelayProofProcessingCursor` is set to (ParaId, SubscribedKey)

#### Scenario: Cursor resumption with wrap-around

- **GIVEN** `RelayProofProcessingCursor` was set to (Publisher B, Key 2) in the previous block
- **AND** subscriptions are ordered as: [(Publisher A, [K1, K2]), (Publisher B, [K1, K2, K3]), (Publisher C, [K1])]
- **WHEN** the next block begins processing
- **THEN** processing starts from (Publisher B, Key 2)
- **AND** continues through (Publisher B, Key 3), (Publisher C, Key 1)
- **AND** wraps around to (Publisher A, Key 1), (Publisher A, Key 2), (Publisher B, Key 1)
- **AND** cursor is cleared when all keys have been processed

#### Scenario: Proof validation - all nodes accessed

- **GIVEN** a relay proof is provided to `set_validation_data`
- **WHEN** all `RelayProofExtender` implementations have processed the proof
- **THEN** `AccessedNodesTracker::ensure_no_unused_nodes()` MUST succeed
- **AND** if any nodes were not accessed, the block panics (extraneous data in proof)

#### Scenario: Proof validation - incomplete at weight limit

- **GIVEN** processing returns `ProofProcessingResult::Incomplete`
- **AND** `!meter.can_consume(min_weight)` where `min_weight` is one read + max node/value size
- **WHEN** the proof is validated
- **THEN** this is valid (weight budget was exhausted)
- **AND** `RelayProofProcessingCursor` is set for next block

#### Scenario: Proof validation - incomplete below weight limit

- **GIVEN** processing returns `ProofProcessingResult::Incomplete`
- **AND** `meter.can_consume(min_weight)` is true (weight remains)
- **WHEN** the proof is validated
- **THEN** the block panics (collator is cheating by omitting data that would have fit)

### Requirement: Publisher Prioritization

The subscriber pallet SHALL prioritize system parachains in proof processing.

#### Scenario: System parachain first

- **GIVEN** subscriptions to parachains 1000 (system) and 3000 (public)
- **WHEN** subscriptions are ordered for processing
- **THEN** parachain 1000 is processed before parachain 3000

### Requirement: TTL Expiration

The broadcaster pallet SHALL automatically delete expired keys via `on_idle`. TTL metadata is stored in `TtlData` storage map for efficient scanning, separate from child trie data.

#### Scenario: Key expires

- **GIVEN** key K was published at block 1000 with TTL 100
- **WHEN** block 1100 is reached and `on_idle` runs
- **THEN** key K is deleted from the child trie
- **AND** the corresponding `TtlData` entry is removed
- **AND** `KeyExpired` event is emitted

#### Scenario: Infinite TTL

- **GIVEN** key K was published with TTL 0
- **WHEN** any number of blocks pass
- **THEN** key K is NOT auto-deleted
- **AND** no entry exists in `TtlData` for this key

#### Scenario: TTL reset on update

- **GIVEN** key K was published at block 1000 with TTL 100 (expires at 1100)
- **WHEN** key K is re-published at block 1050 with TTL 200
- **THEN** the new expiration is block 1250 (1050 + 200)
- **AND** `TtlData` is updated with new (ttl, when_inserted)

#### Scenario: TTL change from finite to infinite

- **GIVEN** key K was published with TTL 100
- **WHEN** key K is re-published with TTL 0
- **THEN** the `TtlData` entry is removed
- **AND** key K no longer expires automatically

#### Scenario: Partial cleanup under weight limit

- **GIVEN** 1000 keys are expired
- **WHEN** `on_idle` has weight for only 500 deletions
- **THEN** 500 keys are deleted
- **AND** `TtlScanCursor` is set to (ParaId, key) for resumption
- **AND** next `on_idle` resumes from cursor

### Requirement: Manual Key Deletion

The broadcaster pallet SHALL allow manual deletion of published keys.

#### Scenario: Parachain self-deletion

- **GIVEN** parachain 2000 has published keys [A, B, C]
- **WHEN** the parachain calls `delete_keys([A, B])`
- **THEN** keys A and B are deleted immediately
- **AND** `KeysDeleted` event is emitted with count 2

#### Scenario: Governance force-deletion

- **GIVEN** parachain 2000 has published keys
- **WHEN** root calls `force_delete_keys(2000, [A, B, C])`
- **THEN** the specified keys are deleted
- **AND** `KeysForcedDeleted` event is emitted

### Requirement: Relay Proof Collection

The parachain collator SHALL collect relay state proofs for subscribed keys.

#### Scenario: Proof collection for subscriptions

- **GIVEN** a parachain subscribes to publisher 1000 keys [A, B, C]
- **WHEN** the collator builds a block
- **THEN** the relay state proof includes paths to keys A, B, C in publisher 1000's child trie

#### Scenario: Child trie key derivation

- **GIVEN** publisher parachain ID is 1000
- **WHEN** the child trie storage key is derived
- **THEN** it equals `(b"pubsub", ParaId(1000)).encode()`
- **AND** both broadcaster and subscriber use identical derivation

### Requirement: Proof Processing

The `RelayProofExtender::process_proof()` SHALL process pub-sub proofs with unified logic for both off-chain (pruning in `provide_inherent`) and on-chain (verification in `set_validation_data`).

#### Scenario: Unchanged child tries skipped

- **GIVEN** publisher 1000's child trie root has not changed (per `PreviousPublishedDataRoots`)
- **WHEN** `RelayProofExtender::process_proof()` runs
- **THEN** the entire child trie for publisher 1000 is skipped (no reads)
- **AND** off-chain: the child trie is removed from the proof

#### Scenario: Cached nodes read from storage

- **GIVEN** nodes [N1, N2, N3] are cached in `CachedTrieNodes` for publisher 1000
- **WHEN** `RelayProofExtender::process_proof()` traverses a changed child trie
- **THEN** cached nodes are read from storage (tracked automatically via host function)
- **AND** off-chain: matching cached nodes are removed from the proof
- **AND** only new/changed nodes are read from the proof

#### Scenario: Unsubscribed key paths not accessed

- **GIVEN** publisher 1000 has keys [A, B, C, D, E] but subscriber only subscribes to [A, B]
- **WHEN** `RelayProofExtender::process_proof()` runs
- **THEN** only paths to keys [A, B] are accessed
- **AND** off-chain: nodes leading only to keys [C, D, E] are removed from the proof

#### Scenario: Depth limit enforced during processing

- **GIVEN** `MaxTrieDepth` is 8
- **AND** publisher 1000 has a key path requiring traversal depth of 10
- **WHEN** `RelayProofExtender::process_proof()` runs
- **THEN** traversal stops at depth 8
- **AND** the entire publisher 1000 is disabled
- **AND** publisher 1000 is added to `DisabledPublishers` storage

#### Scenario: Budget limit enforced with combined tracking

- **GIVEN** 1 MiB budget for pub-sub (proof + cache reads combined)
- **AND** processing would read 600 KB from proof and 600 KB from cache
- **WHEN** `meter.consumed()` exceeds 1 MiB in `proof_size`
- **THEN** processing stops at current key
- **AND** off-chain: remaining nodes are removed from the proof
- **AND** `RelayProofProcessingCursor` is set for resumption
