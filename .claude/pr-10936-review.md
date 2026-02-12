# PR #10936: pallet-revive: EIP-7702 Set EOA Account Code (continued)

## Overview

This PR implements EIP-7702 for `pallet-revive`, allowing EOAs to delegate code execution to contract addresses via authorization tuples in transactions. The key changes are:

1. **New `AccountType::EOA` variant** with `delegate_target` and `contract_info` fields (replaces the simple unit-variant `EOA`)
2. **Authorization processing** (`evm/eip7702.rs`) — signature recovery, nonce/chain-id validation, delegation set/clear
3. **New dispatchable** `eth_call_with_authorization_list` (call index 13)
4. **Storage deposit accounting** — delegated EOAs get their own child trie & base deposit
5. **Code refcount management** for delegation targets
6. **Migration v3** to re-encode existing `AccountInfoOf` entries
7. **RLP codec fix** for 7702 signed transactions (field ordering was wrong)
8. **Removal of `k256` dependency** in favor of `sp_core::ecdsa::Pair`
9. **Comprehensive test suite** (~1234 lines) covering delegation, deposits, refcounts, selfdestruct, chains, dry-run, etc.

## Issues & Suggestions

### Potential Correctness Issues

1. **`process_authorizations` charges ED from `origin` for new accounts but the storage deposit for `set_delegation` also comes from `origin`**
   In `eip7702.rs:106-112`, the deposit is charged to the *authority's* account (`&account_id`) but funded by the `origin`. If the origin runs out of balance mid-loop (many authorizations), earlier delegations succeed but later ones fail with `DispatchError`, which rolls back the *entire* extrinsic. This is the correct Substrate behavior, but it means partial authorization processing is not possible — consider whether the spec expects invalid auths to be silently skipped (like the chain-id/nonce/signature checks) vs. deposit failures to be hard errors.

2. **`set_delegation` mutates storage unconditionally even when target is not a contract**
   At `storage.rs` `set_delegation`, when delegating to an EOA (no `target_code_hash`), the code updates `delegate_target` to `Some(target)` but does *not* clear an existing `contract_info` from a prior delegation to a contract. This means after delegating to contract A then to EOA B, the `contract_info` from A remains with a stale `code_hash`. The `old_code_hash` is still correctly decremented, but the stale `ContractInfo` in storage could confuse readers. Consider explicitly clearing `contract_info` when `target_code_hash` is `None` and the old delegation had one.

3. **`clear_delegation` refunds `storage_base_deposit` but does not clear `storage_byte_deposit` / `storage_item_deposit`**
   If a delegated EOA wrote storage items (via the delegated contract), those deposits are held. `clear_delegation` only refunds `storage_base_deposit` and zeros `code_hash`, but the per-item and per-byte deposits remain. This seems intentional (storage persists for re-delegation), but it means the held funds for user-written storage are never released until... when exactly? There's no explicit cleanup path documented.

4. **Benchmark linear range discrepancy**: `process_new_account_authorization` goes up to `n=1000` but `process_existing_account_authorization` only goes to `n=255`. The comment says "0 to 255 as per EIP-7702" for the latter, but EIP-7702 doesn't specify a 255 limit on authorization list length (only a practical one). The new-account variant uses 1000. These should be consistent.

### Design Observations

5. **`eth_call` now delegates to `eth_call_impl` but `eth_call_with_authorization_list` is the "real" one**
   The old `eth_call` (call index 4) now just calls `eth_call_impl` with an empty auth list. The `into_call` in `call.rs:163` always generates `eth_call_with_authorization_list` even for non-7702 transactions (with empty auth list). This means all Ethereum transactions now go through the auth-list path. This is fine but adds minor overhead to every tx (the weight annotation includes `process_new_account_authorization(0)`). Worth noting in the PR description.

6. **`worst_case_delegation_deposit` is extremely conservative**
   It assumes `max_code_size` for the code lockup deposit per authorization. In practice, the delegated contract's code is already uploaded and its size is known. This over-estimation means gas estimates for 7702 transactions will be inflated. This is safe but could be improved.

7. **`new_for_delegation` uses a different trie derivation than regular contracts**
   Regular contracts use `("contract_child_trie_v1", next_trie_seed)` while delegated accounts use `("delegated_trie_v1", address)`. The address-based derivation is correct (storage persists across re-delegations) but creates a new convention. Good.

### Minor / Style

8. **`signing_message` capacity hint** (`eip7702.rs:131`): `Vec::with_capacity(1 + 64)` — the RLP output is variable-length. 65 bytes is likely an underestimate for the RLP encoding of `(chain_id, address, nonce)` which is ~26+ bytes for address alone. Not a bug (Vec grows), just a misleading hint.

9. **Debug log in `runtime.rs:137-141`** — the `eth_transact substrate tx hash` log was added but seems like a leftover debug statement. Consider removing or gating behind a more specific target.

10. **`Counter.sol` changed from `uint256` to `uint64`** — this changes the storage layout of the fixture contract, which is why the prestate-diff tracing test expectations changed (slot packing). This is fine but worth calling out as an intentional change in the PR description since it affects existing tests.

11. **`process_authorizations` log message at line 82** says `"expected {expected_nonce:?}, got {current_nonce:?}"` but semantically it's the authorization that provides the expected nonce and the chain provides the current one. The wording could be clearer: "authority nonce is {current_nonce}, authorization specified {expected_nonce}".

### Test Coverage

The test suite is thorough. Good coverage of:
- Signature validation, chain-id, nonce edge cases
- Delegation set/clear/re-delegation round-trips
- Storage persistence across re-delegation
- Deposit charging/refunding
- Code refcount management
- EXTCODEHASH/EXTCODESIZE for delegated accounts
- Delegation chains not being followed
- SELFDESTRUCT behavior on delegated accounts
- Dry-run gas estimation with auth lists

**Missing test coverage:**
- What happens if the same authority appears in the auth list with *sequential* nonces (nonce N, then nonce N+1)? The first increments the nonce, so the second should succeed. This would be a useful test.
- Error path when `charge_deposit` fails mid-authorization-list (origin out of funds)

## Summary

Solid implementation with good spec adherence and excellent test coverage. The main items to address are:
- **Item 2**: Stale `contract_info` when re-delegating from contract to EOA target
- **Item 3**: Document the lifecycle of per-item/per-byte storage deposits for delegated accounts
- **Item 4**: Align benchmark ranges
- **Item 9**: Remove debug log or make it intentional
