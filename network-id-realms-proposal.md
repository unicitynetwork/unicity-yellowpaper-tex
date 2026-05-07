# Network IDs and Realms — Proposal vs. Current Yellowpaper

**TL;DR.** Today the yellowpaper treats the network identifier `α` as a single tag attached to a token at mint time and verified once against the verifier's trust base. The proposal turns `α` into a hard, per-state cryptographic binding to a specific Unicity oracle, derives token IDs and addresses from `α`, and groups networks into globally agreed *realms* so a token can move across multiple oracles within one realm without any party having to negotiate trust.

## What the yellowpaper says today (network-id branch, before this proposal)

- **Network ID = mint-time tag.** `D_mint = (α, ν', id, ty, reason, aux')`. `α` "binds the token to a specific Unicity network instance" (`execution-layer.tex:69`).
- **One trust base, one network.** Transfer verification checks `π.UC.α = T.α` and the token verifier rejects upfront if `T₀.D_mint.α ≠ T.α` (`execution-layer.tex:129`, `:151`). The verifier already decided which network it trusts; the token must match it.
- **Predicates know nothing about `α`.** `ν_sig(pk; ·)`, `ν_p2pkh(h_pk; ·)`, etc. The predicate is only a spending condition; the network binding is enforced one layer up.
- **Token ID is free-form.** `id ∈ I`, "unique within network α". The minter chooses it; the protocol only checks that the SMT key derived from it isn't already taken.
- **Implicit assumption.** A token lives entirely under one `α` from genesis to burn; splitting requires the same `α`.

## What the proposal changes

1. **Predicates carry `α` as a mandatory first parameter** — `ν_sig(α, pk; ·)`, `ν_p2pkh(α, h_pk; ·)`, etc. `α` enters the canonical predicate encoding `EncPred(ν)`, so it enters `sid = H(EncPred(ν), s_th)`. Two networks therefore cannot share a spent-state registry even by accident: the same logical owner key under different `α` produces different `sid`s.

2. **The network check moves from "trust base" to "predicate"** — transfer verification becomes `π.UC.α = ν.α` (not `= T.α`). A unicity proof from the wrong oracle MUST be rejected even if it is otherwise perfectly valid. Closes the cross-network double-spend window where two oracles could each certify a different spend of the "same" state.

3. **Addresses bind `α`** — for unlock-pubkey predicates, the user-facing address becomes `addr(α, pk) = H(ADDR_TAG, α, pk)`. SDKs refuse to encode an address without `α` and refuse to build a transaction whose recipient predicate's `α` doesn't match the address's `α`.

4. **Token ID is derived, not chosen** — `id = H(TOKENID_TAG, α_genesis, salt)`. The mint-tx field `id` is replaced by a 256-bit `salt`. `id` provably commits to `α_genesis`; under collision-resistance no `id` can belong to two different networks. Per-network uniqueness (already guaranteed by each oracle) therefore becomes *global* uniqueness for free.

5. **Realms** — new concept. A realm `R ⊆ A` is a publicly fixed, SDK-hardcoded set of network identifiers whose oracles are mutually accepted. Three are defined:
   - **MAINNET** — production networks proving real-value tokens.
   - **TESTNET** — networks for tokens with no real value.
   - **PRIVATE** — networks for custom / consortium projects.
   
   Realms are pairwise disjoint. A token is bound to one realm at genesis (new field `R` in `D_mint`) and stays in it for life: every per-state `α` along the history must lie in `R`. Inside one realm, consecutive states MAY use different `α`s — tokens can hop between mutually-trusted oracles without any verifier having to make an ad-hoc trust decision.

## Why it matters

- **Eliminates cross-network double-spend by construction.** Today, two cooperating-but-not-coordinated oracles can each accept a conflicting spend of the same state, and the conflict is only caught when one verifier happens to look at both proofs. With predicate-bound `α`, the conflicting proofs are unspendable in the wrong network from the start.
- **Makes "moving between networks" a first-class operation.** Today, sending a token from network 1 to network 2 isn't really defined — the token's `α` stays fixed, and network-2 verifiers reject it. With realms, intra-realm hops are explicitly allowed and explicitly bounded.
- **Replaces "honor-system" trust with mechanical rules.** Realm membership is hardcoded in the SDK and not negotiable per token. Verifiers don't need to know the operator of network 7 to decide whether to accept its proofs — they just check `7 ∈ R`.

## Compatibility note

The wire format changes: `D_mint` gains `R` and replaces `id` with `salt`; `EncPred` gains a network-id field. Existing tokens minted under the old format are not forward-compatible without a deterministic migration mapping (e.g. `id = old_id`, `salt = old_id`, plus a flag day per network). Out of scope for this proposal.

---

## Minimal SDK / consumer amendments

Initial deployment runs **exactly one** Unicity oracle per public realm:

| Realm     | Networks (now)        | Networks (future) |
|-----------|-----------------------|-------------------|
| MAINNET   | `{1}`                 | open              |
| TESTNET   | `{2}`                 | open              |
| PRIVATE   | `{}` (per-deployment) | open              |

Because each realm currently has at most one `α`, the SDK does not need a multi-oracle network selector, a per-`α` trust-base table, or any operator-discovery code. The amendments below are the smallest changes that put the realm/`α` binding in place today and let multi-oracle support drop in later without re-breaking the wire format.

### 1. SDK constants module

Add three hardcoded items. These are public, immutable, and MUST NOT be reconfigurable at runtime:

```text
TOKENID_TAG = SHA-256("UNICITY_TOKENID_v1")     # 32 bytes
ADDR_TAG    = SHA-256("UNICITY_ADDR_v1")        # 32 bytes

REALMS = {
  MAINNET: {1},
  TESTNET: {2},
  PRIVATE: {},        # opt-in, populated per private deployment
}
# Reverse lookup, derived at startup:
NETWORK_REALM = { 1: MAINNET, 2: TESTNET, ... }
```

Provide a helper `realm_of(α) -> Realm` that throws on unknown `α`.

### 2. Predicate model

For every built-in predicate (`sig`, `p2pkh`, `p2sh`, `msig`, `tsig`, `burn`, `tlock`, `htlc`):

- Add an `α: NetworkId` field as the **first** parameter.
- Constructor signatures change from `Sig(pk)` to `Sig(α, pk)`, etc. Provide a thin wrapper `Sig.for_realm(realm, pk)` that picks `α` as the unique element of `REALMS[realm]` (and throws if the realm has zero or multiple networks — future-proofing).
- Update the canonical CBOR encoding to a **four**-element top-level array `[engine, type_code, α, params]` (was three). Decoder rejects three-element legacy arrays.
- Predicate equality stays "byte equality of canonical encoding" — no code change there, but encoded sizes grow by ~3 bytes.
- Expose `predicate.alpha` and `predicate.realm` accessors.

### 3. Address derivation

- Replace any `address(pk)` API with `address(α, pk) = SHA-256(ADDR_TAG ‖ α ‖ pk)`.
- Address codec (Bech32 or whatever the SDK uses) must encode `α` alongside the hash, so that consumers reading an address learn `α` without out-of-band data. Reject addresses with no `α`.
- Wallet UX: receive-address generation requires the user (or app) to pick a realm; in single-`α`-per-realm mode the SDK fills `α` automatically.

### 4. Mint transaction builder

- Builder API change: `mint(α, predicate, id, ty, reason, aux)` → `mint(realm, predicate, salt, ty, reason, aux)`, with:
  - `α` derived as the unique element of `REALMS[realm]`;
  - `salt` defaulting to `os.urandom(32)` if not supplied;
  - `id` computed internally as `SHA-256(TOKENID_TAG ‖ α ‖ salt)`;
  - `predicate.alpha` asserted to equal `α`.
- Update CBOR `D_mint` from 6-tuple `(α, ν', id, ty, reason, aux)` to 7-tuple `(R, α, ν', salt, ty, reason, aux)` where `R` is the realm constant.

### 5. Token verification (`VerifyToken`)

Three new checks; one tightened check. All cheap, no I/O.

1. After parsing the mint tx: `R = D_mint.R`; reject if `R` is not a known realm constant or if `D_mint.α ∉ REALMS[R]`.
2. For the mint inclusion proof: enforce `π₀.UC.α == D_mint.α` (was `== trustBase.α`).
3. For each transfer step `i`: enforce `predicateᵢ₋₁.α ∈ REALMS[R]` **and** `πᵢ.UC.α ∈ REALMS[R]`.
4. Tighten transfer verification: replace `π.UC.α == trustBase.α` with `π.UC.α == predicate.α`.

In the single-`α`-per-realm regime today, checks (1), (3), and (4) collapse to comparing constants; they are nonetheless mandatory so future multi-oracle realms work without code changes.

### 6. Trust-base handling

- Today: one trust base per running SDK instance, matched to the one oracle in its realm. No change needed.
- Future-proofing: index trust bases as `T[α]`. For now, `T[α]` returns the single deployed trust base if `α` matches, and `None` otherwise. The token verifier already references `T[predicate.α]` — that's the only call site that needs the indirection.

### 7. Aggregator / oracle-side

The Unicity Service itself doesn't need any change for this proposal: it already stamps its `α` into every Unicity Certificate. The new rules are entirely client-side (state-id derivation now includes `α` via `EncPred`, but the oracle treats the SMT key as opaque).

### 8. Consumer-side changes

- **Wallets** — receive flow passes the active realm; send flow reads `α` from the destination address and asserts the wallet's realm matches.
- **Block explorers / indexers** — index by `(realm, α, id)`; show `id` as derived from `(α, salt)` for new tokens.
- **dApps / custodians** — replace any code path that supplies an explicit `id` with one that supplies a `salt`. If client code was choosing `id = SHA-256(...)` for collision avoidance, just hand those bytes through as `salt` — the SDK will hash them again with `TOKENID_TAG` and `α`.
- **Test fixtures** — regenerate any hardcoded token IDs and predicate-encoded byte strings; they all change.

### 9. Tests to add

- Reject a token whose mint-tx `R` is not in `REALMS`.
- Reject a token whose mint-tx `α ∉ REALMS[R]`.
- Reject a transfer whose inclusion proof's `α` differs from the spending predicate's `α` (cross-network spend).
- Reject a token whose history references two different realms (synthesize by stitching two valid sub-histories).
- Stability: same `(α, salt)` always derives the same `id`; different `α` with same `salt` derive different `id`s.
- Address: `addr(1, pk) ≠ addr(2, pk)` for any `pk`.

### 10. Migration

Mainnet has not launched, so the cleanest path is a hard cut: roll out the new SDK before mainnet genesis. Testnet tokens minted under the old format can be discarded or re-minted. No on-chain migration code is required.
