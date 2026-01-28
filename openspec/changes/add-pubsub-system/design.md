# Design: Pub-Sub System

## Context

RFC-0160 specifies a publish-subscribe mechanism for cross-chain data sharing via the relay chain. Publishers (parachains) store key-value data in per-publisher child tries on the relay chain. Subscribers (other parachains) declare subscriptions and receive data via relay state proofs included in their inherent data.

Key stakeholders:
- Publisher parachains (e.g., POP for ring signature roots)
- Subscriber parachains (e.g., chains verifying ring proofs)
- Relay chain governance (publisher registration, limits)

Constraints:
- PoV size limits
- Relay chain storage costs
- XCM v5 compatibility required

## Goals / Non-Goals

**Goals:**
- Enable parachains to publish key-value data to relay chain (subject to size limits)
- Enable parachains to subscribe to and receive published data with proofs
- Minimize PoV overhead via trie node caching
- Support TTL-based automatic expiration
- System parachain privilege (publish without registration)

**Non-Goals:**
- Prefix-based key enumeration (subscribers must know exact keys)
- Real-time streaming (latency is 2+ blocks)

## Decisions

### Decision 1: Fixed 32-byte Keys

Keys are 32-byte values. Publishers are responsible for hashing their logical key names before publishing.

**Rationale:**
- Evenly distributed trie structure
- Predictable storage calculations

### Decision 2: Per-Publisher Child Tries

Each publisher gets a dedicated child trie under key `(b"pubsub", para_id).encode()`.

**Rationale:**
- Prevents unbalanced main trie
- Efficient cleanup on deregistration
- Child trie roots enable change detection

### Decision 3: Maximum Trie Depth

A `MaxTrieDepth` parameter limits how deep trie traversal can go. Tries deeper than this limit are not supported.

**Rationale:**
- Bounds the maximum cache size per key (at most `MaxTrieDepth` nodes per key path)
- Prevents unbounded storage growth from pathologically deep tries
- Provides predictable worst-case resource usage
- With 32-byte keys and radix-16 trie, typical depth is ~8-10 nodes

**Recommended value:** 16 (sufficient for any reasonable trie structure with 32-byte keys)

**Behavior when exceeded:**
- Proof processing fails with `TrieDepthExceeded` error
- The entire publisher is disabled (added to `DisabledPublishers` storage)
- Disabled publishers are skipped in subsequent blocks
- Manual re-enabling required via `enable_publisher()` call
- This is a configuration/pathological case, not expected in normal operation

### Decision 4: On-Chain Trie Node Caching

Subscriber parachain caches trie nodes (structure only) needed to access subscribed keys in `CachedTrieNodes` storage (keyed by ParaId + H256 node hash). Cache size is bounded by `MaxTrieDepth * num_subscribed_keys`.

**V1 Trie Format:**
- Data larger than 32 bytes is stored externally (hash reference in trie node)
- Data 32 bytes or smaller may be inlined in the trie node
- Cache stores only trie structure nodes, NOT the external data
- This keeps cache entries small and predictable

**Storage:**
```rust
#[pallet::storage]
pub type CachedTrieNodes<T: Config> = StorageDoubleMap<
    _,
    Blake2_128Concat, ParaId,
    Blake2_128Concat, H256,
    BoundedVec<u8, ConstU32<750>>,  // Max trie node size (see calculation below)
>;
```

**Trie Node Size Calculation (V1 Layout with Blake2-256):**

Branch nodes (worst case) consist of:
- Header: 5 bytes (variable-length nibble count encoding)
- Partial key: 32 bytes (max for 64 nibbles with 32-byte keys)
- Bitmap: 2 bytes (which of 16 children exist)
- Value: 32 bytes (either inline value with compact length, or 32-byte hash reference)
- Children: 16 × 33 bytes = 528 bytes (32-byte hash + 1-byte compact length each)

Note: `TRIE_VALUE_NODE_THRESHOLD = 33` means values are inlined only if their encoded size (value + compact length) fits in 32 bytes. Larger values are stored externally with a 32-byte hash reference.

**Total worst case: 5 + 32 + 2 + 32 + 528 = 599 bytes**

Using 750 bytes provides ~25% safety margin for any edge cases.

**Rationale:**
- Trie nodes without external data are bounded in size
- External data is always fetched fresh from the proof (not cached)
- Data consumers can cache the data or not, depending on their needs
- Reduces on-chain storage requirements significantly

**RelayProofExtender trait:**

A trait for extending relay proof collection and processing. The trait handles:
1. Declaring which keys to include in the proof (via `relay_keys()`)
2. Processing the proof on-chain with access tracking (via `process_proof()`)

**Integration:** The `RelayProofExtender` is configured as a parameter of the `parachain_system::Config` trait. The pub-sub subscriber pallet implements this trait, allowing parachain-system to call it during proof collection and verification.

**Critical invariant: All requested keys must be read**

Every key returned by `relay_keys()` MUST be read from the proof during `process_proof()`. After processing, the runtime validates that every node in the proof was accessed. Unread nodes cause block validation to fail (prevents including extraneous data in the proof).

**Critical: PoV size includes both relay proof AND parachain storage**

The total PoV contribution is: `relay_proof_size + parachain_storage_proof_size`

The same logic runs in both `provide_inherent` (off-chain) and `set_validation_data` (on-chain) to ensure they stay in sync.

```rust
pub trait RelayProofExtender {
    /// Returns relay storage keys to include in the proof.
    /// Called by `ParachainSystem::relay_keys_to_prove()` which is used by
    /// the runtime's `KeyToIncludeInRelayProof` implementation.
    /// 
    /// Every key returned here MUST be read during `process_proof()`.
    /// Unread proof nodes cause block validation failure.
    fn relay_keys() -> RelayProofRequest;
    
    /// Processes the relay proof for keys returned by `relay_keys()`.
    /// 
    /// Must read all requested keys, or return `Incomplete` if weight
    /// is exhausted. Unread proof nodes cause block validation failure.
    fn process_proof(
        db: &MemoryDB<Blake2Hasher>,
        relay_root: H256,
        tracker: &mut AccessedNodesTracker<H256>,
        meter: &mut WeightMeter,
        mode: ProcessingMode,
    ) -> ProofProcessingResult;
}

/// No-op implementation for parachains that don't need relay proof extension.
impl RelayProofExtender for () {
    fn relay_keys() -> RelayProofRequest {
        RelayProofRequest::default()
    }
    
    fn process_proof(
        _db: &MemoryDB<Blake2Hasher>,
        _relay_root: H256,
        _tracker: &mut AccessedNodesTracker<H256>,
        _meter: &mut WeightMeter,
        _mode: ProcessingMode,
    ) -> ProofProcessingResult {
        ProofProcessingResult::Complete
    }
}

pub enum ProcessingMode {
    /// Off-chain: determine what fits in budget
    Prune,
    /// On-chain: process proof and update state
    Verify,
}

pub enum ProofProcessingResult {
    /// All subscribed keys were processed
    Complete,
    /// Budget exhausted before completing.
    /// 
    /// Validation requirement: `!meter.can_consume(min_weight)` where min_weight = one read + max(MaxValueSize, MaxTrieNodeSize)
    /// must hold, otherwise the block fails validation (collator omitted data that would have fit).
    Incomplete,
}
```

**Weight Tracking:**

Weight consists of two components:
1. **ref_time** - computational time, tracked via benchmarked weights for storage operations
2. **proof_size** - storage proof size, tracked automatically for parachain storage and manually for relay proof

We use the standard `WeightMeter` from `sp_weights` to track both components. The meter is shared across all `RelayProofExtender` implementations.

**Relay Proof Access Tracking:**

We reuse existing infrastructure from `sp_trie` and bridges:
- `AccessedNodesTracker` from `sp_trie::accessed_nodes_tracker` - implements `TrieRecorder` to track which nodes have been accessed
- `ensure_no_unused_nodes()` - validates all proof nodes were read (no extraneous data)

```rust
use sp_trie::accessed_nodes_tracker::AccessedNodesTracker;

// Create tracker with proof node count
let mut tracker = AccessedNodesTracker::<H256>::new(proof.len());

// Use with trie operations - automatically records accessed nodes
let trie = TrieDBBuilder::<LayoutV1<H>>::new(&db, &root)
    .with_recorder(&mut tracker)
    .build();

// After processing, verify all nodes were accessed
tracker.ensure_no_unused_nodes()?;
```

**Weight consumption for relay proof reads:**

When reading from relay proof, consume weight for both ref_time (benchmarked) and proof_size (actual):

```rust
// For each relay proof node read
let weight = T::DbWeight::get().reads(1)
    .saturating_add(Weight::from_parts(0, node_size as u64));
meter.consume(weight);
```

**Note:** Parachain storage reads (including `CachedTrieNodes`) are tracked automatically by the `storage_proof_size()` host function and reclaimed via `StorageWeightReclaimer`. Relay proof reads must be tracked manually since they come from a separate proof structure.

**Block building process (in `provide_inherent`):**

1. **Collect extra keys:** The collator calls `KeyToIncludeInRelayProof::keys_to_prove()` runtime API (already exists in `cumulus_primitives_core`). The runtime implements this trait and calls `ParachainSystem::relay_keys_to_prove()` to get pub-sub keys.

2. **Build initial proof:** Node builds proof containing all requested keys.

3. **Process proof:** Call `RelayProofExtender::process_proof()` with `ProcessingMode::Prune`. When budget is exhausted, remove unprocessed data from proof.
   
4. **Priority ordering when budget constrained:** System parachains (ID < 2000) first, then non-system in randomized order (seeded by block hash).

**Runtime integration (following `CollectCollationInfo` pattern):**

The runtime implements the existing `KeyToIncludeInRelayProof` runtime API trait and delegates to parachain-system:

```rust
// In runtime's lib.rs, inside impl_runtime_apis! block:
impl cumulus_primitives_core::KeyToIncludeInRelayProof<Block> for Runtime {
    fn keys_to_prove() -> cumulus_primitives_core::RelayProofRequest {
        // Delegate to parachain-system (same pattern as CollectCollationInfo)
        ParachainSystem::relay_keys_to_prove()
    }
}
```

**Parachain-system helper function:**

```rust
// In cumulus/pallets/parachain-system/src/lib.rs
impl<T: Config> Pallet<T> {
    /// Returns relay storage keys to include in the proof.
    /// Delegates to `T::RelayProofExtender::relay_keys()`.
    ///
    /// This is expected to be used by the
    /// [`KeyToIncludeInRelayProof`](cumulus_primitives_core::KeyToIncludeInRelayProof) runtime api.
    pub fn relay_keys_to_prove() -> RelayProofRequest {
        T::RelayProofExtender::relay_keys()
    }
}
```

**Subscriber pallet implementation:**

```rust
impl<T: Config> Pallet<T> {
    /// Returns relay storage keys needed for subscribed publishers.
    /// Called by parachain-system via `RelayProofExtender` trait.
    pub fn relay_keys() -> RelayProofRequest {
        let (subscriptions, _) = T::SubscriptionHandler::subscriptions();
        
        let keys = subscriptions.iter()
            .filter(|(id, _)| !DisabledPublishers::<T>::contains_key(id))
            .map(|(publisher_id, _keys)| {
                RelayStorageKey::Child {
                    storage_key: derive_child_storage_key(*publisher_id),
                    key: Vec::new(), // Empty = entire child trie
                }
            })
            .collect();
        
        RelayProofRequest { keys }
    }
}
```

**On-chain verification (in `set_validation_data`):**

```rust
fn verify_relay_proof(
    relay_root: H256,
    proof: RawStorageProof,
    weight_limit: Weight,
) -> Result<(), Error> {
    let proof = StorageProof::new_with_duplicate_nodes_check(proof)?;
    let mut tracker = AccessedNodesTracker::<H256>::new(proof.len());
    let db = proof.into_memory_db();
    
    let mut meter = WeightMeter::with_limit(weight_limit);
    
    // 1. Process static keys (validation data, etc.) - automatic
    process_static_relay_keys(&db, relay_root, &mut tracker, &mut meter)?;
    
    // 2. RelayProofExtender processes the proof (Config parameter of parachain-system)
    let result = T::RelayProofExtender::process_proof(
        &db,
        relay_root,
        &mut tracker,
        &mut meter,
        ProcessingMode::Verify,
    );
   
    // 3. Verify proof integrity
    
    // All nodes in proof must be accessed (no extraneous data)
    tracker.ensure_no_unused_nodes()?;
    
    // If processing was incomplete, weight must be at limit
    if matches!(pubsub_result, ProofProcessingResult::Incomplete) {
        let min_missing_weight = Weight::from_parts(
            0,
            max(T::MaxValueSize::get(), T::MaxTrieNodeSize::get()) as u64,
        );
        ensure!(
            !meter.can_consume(min_missing_weight),
            Error::IncompleteProofBelowLimit
        );
    }
    
    Ok(())
}
```

**Key validation rules:**
1. **All proof nodes must be accessed** - no extraneous/unused data allowed
2. **Missing nodes only valid at budget limit** - if `proof_size + max(max_value_size, max_node_size) > max_budget`, missing nodes are acceptable
3. **Missing nodes below limit = invalid block** - collator is cheating by omitting required data

**SubscriptionHandler trait:**

```rust
pub trait SubscriptionHandler {
    /// Returns current subscriptions.
    /// Keys can be added freely. Keys SHOULD NOT be removed - if removed,
    /// call `clear_publisher_cache` dispatchable to clean up stale nodes.
    fn subscriptions() -> (Vec<(ParaId, Vec<SubscribedKey>)>, Weight);
    
    /// Called when a subscribed key's value changes.
    fn on_data_updated(publisher: ParaId, key: SubscribedKey, value: &[u8], ttl: TtlState) -> Weight;
}
```

**Cache management dispatchable:**

```rust
/// Clears all cached trie nodes for a publisher. Call this after removing
/// subscriptions to free storage. The cache will be rebuilt on subsequent blocks.
/// 
/// Origin: Signed or governance (configurable via Config::ClearCacheOrigin)
#[pallet::call]
fn clear_publisher_cache(origin: OriginFor<T>, publisher_id: ParaId) -> DispatchResult {
    T::ClearCacheOrigin::ensure_origin(origin)?;
    
    // Remove all cached nodes for this publisher
    let _ = CachedTrieNodes::<T>::clear_prefix(publisher_id, u32::MAX, None);
    
    // Clear the stored root so next block fetches fresh data
    PreviousPublishedDataRoots::<T>::remove(publisher_id);
    
    Self::deposit_event(Event::PublisherCacheCleared { publisher_id });
    Ok(())
}
```

**Subscriber pallet implementation of RelayProofExtender:**

```rust
impl<T: Config> RelayProofExtender for Pallet<T> {
    fn relay_keys() -> RelayProofRequest {
        let (subscriptions, _) = T::SubscriptionHandler::subscriptions();
        
        let keys = subscriptions.iter()
            .filter(|(id, _)| !DisabledPublishers::<T>::contains_key(id))
            .map(|(publisher_id, _keys)| {
                RelayStorageKey::Child {
                    storage_key: derive_child_storage_key(*publisher_id),
                    key: Vec::new(), // Empty = entire child trie
                }
            })
            .collect();
        
        RelayProofRequest { keys }
    }
    
    fn process_proof(
        db: &MemoryDB<Blake2Hasher>,
        relay_root: H256,
        tracker: &mut AccessedNodesTracker<H256>,
        meter: &mut WeightMeter,
        mode: ProcessingMode,
    ) -> ProofProcessingResult {
        let cursor = RelayProofProcessingCursor::<T>::take();
        let (subscriptions, _) = T::SubscriptionHandler::subscriptions();
        
        // Combine subscriptions by publisher and deduplicate keys
        // Multiple subscribers may subscribe to the same publisher
        let mut combined: BTreeMap<ParaId, BTreeSet<SubscribedKey>> = BTreeMap::new();
        for (publisher_id, keys) in &subscriptions {
            if DisabledPublishers::<T>::contains_key(publisher_id) {
                continue;
            }
            combined.entry(*publisher_id)
                .or_default()
                .extend(keys.iter().cloned());
        }
        
        // Build ordered list of (publisher_id, key) pairs to process
        let mut work_items: Vec<(ParaId, SubscribedKey)> = Vec::new();
        for (publisher_id, keys) in &combined {
            for key in keys {
                work_items.push((*publisher_id, key.clone()));
            }
        }
        
        // Find cursor position and rotate work_items to start from there
        let start_idx = if let Some((cursor_pub, ref cursor_key)) = cursor {
            work_items.iter()
                .position(|(pub_id, key)| *pub_id == cursor_pub && key == cursor_key)
                .unwrap_or(0)
        } else {
            0
        };
        
        // Process items starting from cursor, wrapping around to beginning
        let rotated: Vec<_> = work_items.iter()
            .cycle()
            .skip(start_idx)
            .take(work_items.len())
            .collect();
        
        // Track which publishers we've already read the root for
        let mut publisher_roots: BTreeMap<ParaId, Option<H256>> = BTreeMap::new();
        
        for (publisher_id, key) in rotated {
            // Get or fetch the child trie root for this publisher
            let new_child_root = match publisher_roots.entry(*publisher_id) {
                Entry::Occupied(e) => match e.get() {
                    Some(root) => *root,
                    None => continue, // Publisher has no child trie or unchanged
                },
                Entry::Vacant(e) => {
                    let child_trie_key = derive_child_info(*publisher_id);
                    let trie = TrieDBBuilder::<LayoutV1<Blake2Hasher>>::new(db, &relay_root)
                        .with_recorder(tracker)
                        .build();
                    
                    match trie.get(&child_trie_key) {
                        Ok(Some(root_bytes)) => {
                            let node_size = root_bytes.len();
                            let weight = T::DbWeight::get().reads(1)
                                .saturating_add(Weight::from_parts(0, node_size as u64));
                            if !meter.can_consume(weight) {
                                RelayProofProcessingCursor::<T>::put((*publisher_id, key.clone()));
                                return ProofProcessingResult::Incomplete;
                            }
                            meter.consume(weight);
                            
                            let new_root = H256::from_slice(&root_bytes);
                            let old_root = PreviousPublishedDataRoots::<T>::get(publisher_id)
                                .unwrap_or(EMPTY_TRIE_ROOT);
                            
                            if new_root == old_root {
                                e.insert(None); // Mark as unchanged
                                continue;
                            }
                            
                            e.insert(Some(new_root));
                            new_root
                        }
                        Ok(None) | Err(_) => {
                            RelayProofProcessingCursor::<T>::put((*publisher_id, key.clone()));
                            return ProofProcessingResult::Incomplete;
                        }
                    }
                }
            };
            
            let old_child_root = PreviousPublishedDataRoots::<T>::get(publisher_id)
                .unwrap_or(EMPTY_TRIE_ROOT);
            
            // Process single key
            match process_single_key(
                *publisher_id,
                old_child_root,
                new_child_root,
                db,
                tracker,
                meter,
                key,
                mode,
            ) {
                Ok(changed) => {
                    if changed && matches!(mode, ProcessingMode::Verify) {
                        PreviousPublishedDataRoots::<T>::insert(publisher_id, new_child_root);
                    }
                }
                Err(IncompleteProof) => {
                    RelayProofProcessingCursor::<T>::put((*publisher_id, key.clone()));
                    return ProofProcessingResult::Incomplete;
                }
                Err(TrieDepthExceeded) => {
                    if matches!(mode, ProcessingMode::Verify) {
                        DisabledPublishers::<T>::insert(*publisher_id, DisableReason::TrieDepthExceeded);
                        Pallet::<T>::deposit_event(Event::PublisherDisabled {
                            publisher_id: *publisher_id,
                            reason: DisableReason::TrieDepthExceeded,
                        });
                    }
                    // Mark publisher as having no valid root to skip remaining keys
                    publisher_roots.insert(*publisher_id, None);
                }
            }
        }
        
        ProofProcessingResult::Complete
    }
}
```

**Dual-trie traversal with data extraction:**

Uses `RawTrieIterator` for direct access to trie nodes. The key optimization: **when a node hash in the new trie matches a cached node, the entire subtree is unchanged** - we can skip traversing that branch entirely.

This means for a trie with 5,000 elements where only a few changed:
- Start at root, compare hashes
- If a branch node matches → skip entire subtree (potentially thousands of elements)
- Only traverse paths where nodes differ
- Only deliver `on_data_updated` for actually changed values

All relay proof node accesses go through the `MemoryDB` with `AccessedNodesTracker` recorder to ensure proper access tracking.

```rust
/// Process a single subscribed key. Returns Ok(true) if value changed, Ok(false) if unchanged.
fn process_single_key<T: Config>(
    publisher_id: ParaId,
    old_root: H256,
    new_root: H256,
    db: &MemoryDB<Blake2Hasher>,
    tracker: &mut AccessedNodesTracker<H256>,
    meter: &mut WeightMeter,
    key: &SubscribedKey,
    mode: ProcessingMode,
) -> Result<bool, ProcessingError> {
    let depth_limit = T::MaxTrieDepth::get();
    let cache_db = CachedTrieNodesDB::<T>::new(publisher_id);
    
    // Check if budget sufficient before starting
    let min_weight = T::DbWeight::get().reads(1)
        .saturating_add(Weight::from_parts(0, T::MaxTrieNodeSize::get() as u64));
    if !meter.can_consume(min_weight) {
        return Err(IncompleteProof);
    }
    
    // Old trie iterator reads from on-chain cache (cache reads tracked by host function)
    let mut old_iter = RawTrieIterator::new(&cache_db, old_root, key).ok();
    
    // New trie iterator reads from proof db with access tracking
    let child_trie = TrieDBBuilder::<LayoutV1<Blake2Hasher>>::new(db, &new_root)
        .with_recorder(tracker)
        .build();
    let mut new_iter = match RawTrieIterator::new_from_trie(&child_trie, key) {
        Ok(iter) => iter,
        Err(MissingNode(_)) => return Err(IncompleteProof),
        Err(e) => return Err(e.into()),
    };
    
    let mut depth = 0;
    let mut value_changed = false;
    
    loop {
        depth += 1;
        if depth > depth_limit as usize {
            return Err(TrieDepthExceeded);
        }
        
        // Check budget mid-traversal
        let min_weight = T::DbWeight::get().reads(1)
            .saturating_add(Weight::from_parts(0, T::MaxTrieNodeSize::get() as u64));
        if !meter.can_consume(min_weight) {
            return Err(IncompleteProof);
        }
        
        let old_node = old_iter.as_mut().and_then(|i| i.next_raw_node().ok().flatten());
        let new_node = match new_iter.next_raw_node() {
            Ok(Some(node)) => {
                // Consume weight for this proof node read
                let weight = T::DbWeight::get().reads(1)
                    .saturating_add(Weight::from_parts(0, node.encoded_node.len() as u64));
                meter.consume(weight);
                node
            }
            Ok(None) => break,
            Err(MissingNode(_)) => return Err(IncompleteProof),
            Err(e) => return Err(e.into()),
        };
        
        // Check if node is unchanged (exists in cache with same hash)
        if let Some(ref old) = old_node {
            if old.node_hash == new_node.node_hash {
                // Entire subtree unchanged - done with this key
                break;
            }
            // Old node is stale - remove from cache (only in Verify mode)
            if matches!(mode, ProcessingMode::Verify) {
                CachedTrieNodes::<T>::remove(publisher_id, old.node_hash);
            }
        }
        
        // Cache new node (only in Verify mode)
        if matches!(mode, ProcessingMode::Verify) {
            CachedTrieNodes::<T>::insert(
                publisher_id,
                new_node.node_hash,
                new_node.encoded_node.clone()
            );
        }
        
        if new_node.is_leaf {
            value_changed = true;
        }
    }
    
    if value_changed {
        if let Some(value_data) = new_iter.value() {
            // Only call handler in Verify mode
            if matches!(mode, ProcessingMode::Verify) {
                let entry: PublishedEntry<_> = Decode::decode(&mut &value_data[..])?;
                let ttl_state = compute_ttl_state(&entry);
                
                T::SubscriptionHandler::on_data_updated(
                    publisher_id,
                    *key,
                    &entry.value,
                    ttl_state,
                );
            }
        }
    }
    
    Ok(value_changed)
}

/// HashDB implementation that reads from CachedTrieNodes storage.
struct CachedTrieNodesDB<T: Config> {
    publisher_id: ParaId,
    _phantom: PhantomData<T>,
}

impl<T: Config> CachedTrieNodesDB<T> {
    fn new(publisher_id: ParaId) -> Self {
        Self { publisher_id, _phantom: PhantomData }
    }
}

impl<T: Config> HashDB<H256> for CachedTrieNodesDB<T> {
    fn get(&self, key: &H256) -> Option<Vec<u8>> {
        CachedTrieNodes::<T>::get(self.publisher_id, key).map(|v| v.into_inner())
    }
}
```

**Key verification properties:**
- All relay proof node accesses go through `MemoryDB` with `AccessedNodesTracker` recorder
- Proof is validated against `relay_parent_storage_root` from validation data
- `ProofProcessingResult::Incomplete` indicates missing nodes; cursor stored in `RelayProofProcessingCursor`
- After all extenders run, validation ensures:
  - All nodes in proof were accessed via `tracker.ensure_no_unused_nodes()` (no extraneous data)
  - If result is `Incomplete`, `!meter.can_consume(min_weight)` must hold (budget was full)

**Responsibility split:**

| Operation | `provide_inherent` (off-chain) | `set_validation_data` (on-chain) |
|-----------|--------------------------------|----------------------------------|
| Return extra keys via runtime API | ✓ | — |
| Prune unchanged child tries | ✓ | — |
| Exclude cached nodes from proof | ✓ (reads cache) | — |
| Exclude unsubscribed key paths | ✓ | — |
| Enforce size limit | ✓ | — |
| Verify proof against relay root | — | ✓ |
| Track all node accesses | — | ✓ (AccessedNodesTracker) |
| Extract published data from proof | — | ✓ |
| Call `on_data_updated` callback | — | ✓ |
| Update `CachedTrieNodes` | — | ✓ |
| Update `PreviousPublishedDataRoots` | — | ✓ |
| Set/clear `RelayProofProcessingCursor` | — | ✓ |
| Validate all nodes accessed | — | ✓ |
| Validate missing only at budget limit | — | ✓ |
| Disable publishers (depth exceeded) | — | ✓ |
| Panic on invalid proof | — | ✓ |

### Decision 4: Budget Allocation

Pub-sub uses remaining PoV space after message filtering. No minimum budget is guaranteed - pub-sub gets whatever space remains.

**Formula:**
```
allowed_pov_size = validation_data.max_pov_size * 85%  // Existing HRMP limit
size_limit = messages_collection_size_limit            // Initial budget for DMQ
downward_messages.into_abridged(&mut size_limit)       // DMQ consumes from budget
size_limit += messages_collection_size_limit           // Add HRMP budget
horizontal_messages.into_abridged(&mut size_limit)     // HRMP consumes from budget
// size_limit now contains remaining budget for pub-sub
RelayProofExtender::prune_proof(proof, root, size_limit)
```

**Rationale:**
- Follows same pattern as message filtering with `into_abridged(&mut size_limit)`
- No custom constants needed - pub-sub simply uses remaining space
- If block is full, pub-sub gracefully skips (retry next block)
- Integrates naturally with existing `provide_inherent` flow

### Decision 5: TTL with on_idle Cleanup

Keys can have finite TTL (expire after N blocks) or infinite TTL (0 = never expires).

**Storage structures:**

```rust
/// Entry stored in child trie (includes TTL for subscribers)
pub struct PublishedEntry<BlockNumber> {
    pub value: BoundedVec<u8, MaxValueLength>,
    pub ttl: u32,              // 0 = infinite, N = expire after N blocks
    pub when_inserted: BlockNumber,
}

/// TTL metadata for efficient on_idle scanning (only finite TTL keys)
#[pallet::storage]
pub type TtlData<T: Config> = StorageDoubleMap<
    _, Twox64Concat, ParaId,
    Blake2_128Concat, [u8; 32],
    (u32, BlockNumberFor<T>),  // (ttl, when_inserted)
>;

/// Cursor for incremental TTL scanning
#[pallet::storage]
pub type TtlScanCursor<T: Config> = StorageValue<_, (ParaId, [u8; 32])>;
```

**Rationale:**
- Prevents relay chain storage bloat
- Publishers control data lifecycle
- Subscribers receive TTL metadata for freshness decisions via `TtlState` enum
- Duplicate TTL data: `TtlData` for efficient scanning, child trie for subscriber proofs

**Cleanup mechanism:**
- `on_idle` scans `TtlData` storage for keys where `current_block >= when_inserted + ttl`
- Deletes up to `MaxTtlScansPerIdle` (500) keys per block
- Uses `TtlScanCursor` for incremental processing across blocks
- Best-effort expiration (may be delayed 1-2 blocks if weight exhausted)

### Decision 6: Publish Instruction with Dedicated Barrier

XCM `Publish { data: PublishData }` publishes key-value pairs to the relay chain.

**Fee Model:** Uses a dedicated `AllowPublishFrom<T>` barrier (similar to `AllowSubscriptionsFrom`) that:
- Only allows messages containing just the `Publish` instruction
- Enables free execution for publishing without allowing unpaid execution for arbitrary XCM programs
- Filters which origins (parachains) can publish

```rust
/// Allows execution from `origin` if the message contains only `Publish` instructions,
/// up to a configurable maximum count.
/// 
/// - `T`: Filter for allowed origins
/// - `MaxPublishInstructions`: Maximum number of `Publish` instructions allowed per message
pub struct AllowPublishFrom<T, MaxPublishInstructions>(PhantomData<(T, MaxPublishInstructions)>);
impl<T: Contains<Location>, MaxPublishInstructions: Get<u32>> ShouldExecute 
    for AllowPublishFrom<T, MaxPublishInstructions> 
{
    fn should_execute<RuntimeCall>(
        origin: &Location,
        instructions: &mut [Instruction<RuntimeCall>],
        _max_weight: Weight,
        _properties: &mut Properties,
    ) -> Result<(), ProcessMessageError> {
        ensure!(T::contains(origin), ProcessMessageError::Unsupported);
        ensure!(!instructions.is_empty(), ProcessMessageError::BadFormat);
        ensure!(
            instructions.len() <= MaxPublishInstructions::get() as usize,
            ProcessMessageError::StackLimitReached
        );
        
        // All instructions must be Publish
        for inst in instructions.iter() {
            match inst {
                Publish { .. } => {},
                _ => return Err(ProcessMessageError::BadFormat),
            }
        }
        Ok(())
    }
}
```

**Example configuration:**
```rust
parameter_types! {
    pub const MaxPublishInstructions: u32 = 16;
}

type Barrier = (
    AllowPublishFrom<Everything, MaxPublishInstructions>,
    AllowTopLevelPaidExecutionFrom<Everything>,
    // ... other barriers
);
```

**Rationale:**
- Parachains already pay for relay chain resources via coretime/slots
- Dedicated barrier prevents abuse (can't execute arbitrary XCM for free)
- Storage limits in broadcaster pallet provide additional protection
- Follows established pattern (`AllowSubscriptionsFrom`, `AllowHrmpNotificationsFromRelayChain`)

## Risks / Trade-offs

### Risk: PoV Exhaustion Under High Load

Heavy HRMP message blocks may compete with pub-sub for PoV space.

**Mitigation:**
- Minimum 1 MiB budget guarantees pub-sub progress
- Cursor tracks resumption point for next block
- System parachains prioritized in subscription ordering

### Risk: TTL Cleanup Delays

`on_idle` may not have enough weight to clean all expired keys immediately.

**Mitigation:**
- Best-effort expiration (may delay 1-2 blocks)
- Subscribers should check TTL metadata for freshness
- Manual deletion available for immediate removal

## Migration Plan

Not applicable - new capability with no existing implementation.
