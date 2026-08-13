# Root History Accumulator

**One 32-byte field in the Unicity Seal replaces the linear backlink and turns the chain of Unicity Tree roots from a linked list into a random-access authenticated structure.** A single recent seal, verified under the current trust base, then authenticates every root the network has ever certified. It costs **nothing on the wire**: it takes the slot the backlink vacates.

## What it is

The Unicity Seal gains `a_r`: the root of an append-only Merkle accumulator (MMR) over the Unicity Tree roots of all rounds `0..n_r`. Leaves are `H(ROOT_LEAF, n, r_n)`. Two `O(log N)` proofs are defined against it — membership (root `r_n` was certified at round `n`) and prefix consistency (an older accumulator value is a prefix of a newer one).

It is a deterministic function of state the network already agrees on. It introduces no new consensus decision, no new input, and no new liveness dependency — only a new commitment to what was decided anyway.

It also **subsumes and replaces the linear backlink `r_-`**. A backlink names one predecessor and establishes continuity only by being walked, at `O(n)`; prefix consistency against the accumulator establishes that an *entire* earlier history is a prefix of the current one, in `O(log n)` — the stronger statement and the cheaper check. Nothing in the specification ever verified `r_-` against anything; it was signed, never checked. Removing it takes no property with it.

## What it enables

**1. Anchoring that works under asynchronous sharding.** The direct motivation. A state identifier `sid = H(𝑝, sthash)` is a hash, so one token's successive states scatter pseudo-randomly across shards. A shard-root anchor structurally cannot cover another shard's leaf — a token with `m` transitions over `S` shards would need `min(m,S)` anchor certificates, and no amount of re-anchoring reduces that. Anchoring at the seal fixes it because the Unicity Tree commits every shard, and the shard tree carries forward each shard's last certified input record when it has nothing to certify. **Shards never have to be synchronized.**

**2. Compositional proofs — the thing that makes token compression actually constant-size.** Folding an older attestation into a newer one requires authenticating the older anchor against the newer one. With the accumulator that is one prefix-consistency proof; without it, every fold and every ancestor contributes an anchor that must be carried and separately verified, and "constant size" is false. This is the difference between provenance compression working and not working.

**3. No historical trust bases.** Verifying an old Unicity Certificate otherwise means holding the trust base of *its* epoch — the validator set as it was. With the accumulator, authority flows backwards from one seal verified under the *current* trust base. This is what lets a compressed token carry its issuance geneses as *bare mint data*: the proof anchors them, so only the type-specific authorization check runs outside it, and no historical certificate or trust base is needed for any of them.

**4. Old certificates can't be replayed from an abandoned fork.** An old seal presented on its own is only as good as knowing which chain it belongs to. A root proved against the current accumulator is on *this* chain by construction. This is a security improvement independent of compression.

**5. Thin/light verification.** Verify one recent seal, then authenticate arbitrarily many historical inclusion proofs with hashes only. Relevant to wallets syncing, explorers, exchanges validating deposits, bridge vaults, and any batch verifier.

**6. Bridge return proofs get it for free.** The bridge relation shares the anchoring primitive; it also gains reference-time support, which the previous shard-root anchoring could not provide (it had to exclude timelocked predicates).

**7. Retires a roadmap item.** The previous plan wanted "consistency proofs between arbitrary certified roots" from the aggregation layer — a much heavier ask. This replaces it.

**8. Removes a field rather than adding one.** The linear backlink is gone, and with it the standing question of what linking scheme the BFT Core ought to use — the footnote in the specification conceding that `r_-` merely "illustrates the idea that some sort of cryptographic linking is present" is no longer needed. Chain linking is now a stated, checkable property.

## Why it is more efficient

The exchange is **signature verifications for hash compressions**, at roughly two to three orders of magnitude.

| | Before | After |
|---|---|---|
| Certification evidence per leaf | one Unicity Certificate (BFT quorum signature check) | share of one `O(log N)` hash path |
| Signature checks per attestation | one per distinct anchor, plus one per issuance event | **exactly one** |
| Re-anchoring | required, and grows with history | **eliminated** — old anchors are absorbed, not replaced |
| Retained leaf list | 64 bytes/transition, to re-anchor later | **not needed** |

A quorum signature verification is on the order of hundreds of microseconds; ~28 SHA-256 compressions is on the order of one. Paths for leaves in the same round are shared, and distinct rounds batch into one round table.

What remains outside the single signature is the evidence set: one ordinary certified transfer per *direct* source burn — one for a split-descended token, `k` for a `k`-source merge — because a burn postdates the attestation of the source it consumes and so cannot be inside it. Nothing deeper contributes: ancestors' burns are verified inside the relation.

## Overhead

**Unicity Certificate size: no change.** `a_r` (+32 B) replaces `r_-` (−32 B). Every UC carries a seal, and the seal is the same size as before — it simply carries a field that commits the whole history instead of one that named a single predecessor.

**BFT Core node state: under 1 KB.** The retained frontier is one hash per 1-bit of `N`, plus `N` itself. At one round/second, ten years ≈ 2²⁸ rounds → at most 28 peaks (896 B), ~14 on average (~450 B). Negligible beside the shard info the Core already holds for every shard of every partition.

**BFT Core computation: ~14–28 hashes per round.** `O(1)` amortized to merge peaks, `O(popcount N)` to re-bag them into `a_r`, which must be done every round. Microseconds against a one-second round.

**Verifier computation: `O(d·log(1 + N/d) + log N)`** for `d` distinct rounds touched, batched into one round table. This is a genuine asymptotic addition — shard-root anchoring needed none — but shard-root anchoring does not work under sharding at all, and the added hashing is far cheaper than the signature checks it removes.

**Integration cost (the real one).** The accumulator must be replicated consensus state, not a leader's annotation:
- state authenticator becomes `H(r, a)`, so validators vote on it;
- frontier `(P, N)` joins BFT Core state and state transfer;
- recovery accepts a frontier only if it reproduces the highest QC's `commit_state_id`;
- it is **never reset** — not at epoch change, not at trust base change;
- it must be present **from genesis**, so `N = n_r + 1` holds unconditionally. Starting later would make the size `n_r − n₀ + 1` while every verifier computes `n_r + 1`. Retrofitting onto a running Core is not a matter of recomputing — validators keep no persistent chain of past rounds — and would need a separately specified backfill bundle authenticated against old seals;
- epoch-change and trust-base records must bind `H(r, a)`, not `r` alone, or a new validator set inherits no authenticated accumulator continuity;
- speculative HotStuff branches carry a frontier each; only the committed branch advances the durable one.

## Does it need new network services?

One, and it is the weakest kind of dependency there is: an **untrusted root-history proof service**, specified as an aggregation layer function.

- **Why aggregators.** The BFT Core keeps only the frontier and exposes no public interface — its counterparties are aggregators, not relying parties. Aggregators already retain and serve proof material, so this is a query type rather than a new role. And the root history is *network-global*, not shard-specific, so every aggregator of every shard is an equally valid server: sharding does not fragment it, and clients need no shard affinity.
- **Provers query it; verifiers never do.** An attestation carries its anchor seal, round table and every path, so verification is offline. The service is consulted when proofs are *made*, and proving is discretionary background work that can retry or switch servers. Nothing on the transaction path acquires a dependency.
- **It holds no authority and signs nothing.** Every response is checked against a seal the requester verified itself; a bad response fails locally. The worst a server can do is decline. So it replicates without coordination, caches, and can sit behind ordinary CDN infrastructure.
- **~1 GB/year** of append-only public data, plus `O(log N)` frontier.
- **One BFT Core change it forces:** the seal must be published to the aggregation layer *every* round. Certification Responses only reach shards whose input changed, so idle rounds would leave permanent holes — and a single missing round makes every later accumulator value unverifiable. The seal is produced unconditionally anyway, so this is distribution, not computation.

The stream is self-verifying: a receiver checks that each new seal's accumulator follows from its own frontier, so a skipped, reordered or substituted round is detected immediately and by construction. Bootstrapping is one pass — recompute the accumulator over a bulk-downloaded log and compare against a verified seal.

Weigh that against what the accumulator *removes*: the roadmap item wanting consistency proofs between arbitrary certified roots (a stateful, possibly proving service, strictly heavier), historical trust-base retrieval, and holder-side re-anchoring with its retained leaf lists. On balance it reduces infrastructure.

## What if we drop the database and the service entirely?

Suppose no party runs a root-history archive and no client can issue membership, batched-membership or prefix-consistency queries. Clients re-present their leaves through batched inclusion queries instead, and try to deduplicate seals on top of that. This section works out what survives.

### The fact this turns on

**Round `N`'s Unicity Tree already commits every shard, not only the shards that moved.** Certification step 2 carries an unchanged shard's Input Record forward verbatim; steps 3 and 4 then build the shard trees and the Unicity Tree over the whole IR array. So the seal of round `N` already authenticates the last certified SMT root of *every* shard in the network.

What is missing is not the commitment but the *path*. Step 5 responds only to shards whose IR changed, so a shard that has been idle holds a certificate from an older round and has no way to show where its root sits in round `N`'s tree. That path is exactly the "helper sibling hashes": a `CompShardTreeCert` within the partition plus a `CompUnicityTreeCert` across partitions. For 64 shards per partition and 8 partitions that is 9 hashes, **288 bytes**.

And the path is stable. A shard's entry in the Unicity Tree does not change between its own certifications, so a shard whose root was certified at round `n` can be given a valid path for *any* round in `[n, next certification)`. The current round is in that interval for every shard simultaneously, because no shard has certified past it yet. **A common round therefore always exists and needs no rendezvous protocol, no retry loop and no synchrony assumption.** This is the piece that was not obvious: deduplicating the seals is not a scheduling problem, it is a distribution problem.

### The options

`S` shards touched, `d` distinct rounds among their last certifications (`d ≤ min(S, rounds per t2)`), `F` folds absorbed, `q ≈ 67` quorum, seal ≈ 5 KB, `W` retention window in rounds.

| | A. Full archive | B. Bounded ring | C. Path distribution | D. Versioned shard SMT | E. Nothing |
|---|---|---|---|---|---|
| **Accumulator in seal** | yes, used | yes, used | yes, unused | yes, unused | no |
| **Leaf path** | 1 seal + round table + `d` paths | same | 1 seal + `d` paths | 1 seal + `d` paths | `d` seals + `d` paths |
| **Distinct rounds** | `d` | `d` | **1** | **1** | `d` |
| **Verifier signature checks** | 1 | 1 | 1 | 1 | `d` |
| **Fold reconciliation** | prefix, `O(log N)` hashes | prefix within `W`, else seal | seal only | seal only | seal only, or carry `F` seals |
| **In-circuit quorum checks** | 0 | 0 within `W` | `q` per fold | `q` per fold | `q` per fold |
| **Stored history** | ~1 GB/yr + seam frontier | `W × 32 B` | last few rounds of paths | `W` tree versions | none |
| **Who holds it** | archive operator | existing aggregator | existing aggregator | existing shard | nobody |
| **New role** | **yes** | no | no | no | no |
| **BFT Core change** | publish seal every round | publish seal every round | publish seal **and IR vector** every round | publish seal every round | none |

Option A is the specification as written. B keeps everything A does inside a bounded window. C removes the accumulator from the leaf path altogether by publishing enough per round for any party to derive any shard's path. D reaches the same place by making shards serve proofs against historical roots, which is strictly more expensive than C for the same result. E is the do-nothing baseline.

### What each window buys

The retention curve is the whole argument, and it is steeper than it looks.

| `W` | State at 1 round/s | Covers |
|---|---|---|
| one `t2` | tens of bytes | the leaf path, and nothing else |
| 1 hour | 115 KB | folds by a wallet active within the hour |
| 1 day | 2.7 MB | daily background folding |
| 1 year | 1 GB | stale folds, bridge vaults, auditors |

**The leaf path, which every single attestation needs, needs bytes.** The gigabyte exists solely so that an attestation older than the window can still be folded by the cheap route. That is a real consumer, but it is a narrow one, and it has a working fallback.

### What is actually lost

Not wire bytes and not verifier work: C matches A on both, and beats it on the leaf path by removing the round table. What is lost is the security of *old* attestations.

Prefix reconciliation ties an absorbed anchor to the chain the relying party is on at verification time, so a seal from an abandoned branch, or one signed by a validator set compromised after its epoch closed, cannot be substituted. Seal reconciliation accepts any correctly signed seal of that epoch, so an attestation's security becomes "the validator set of the epoch it was anchored in is never compromised, ever". A wallet folding weekly never notices. A bridge vault verifying a three-year-old attestation is trusting a three-year-old committee.

The second loss is optionality on the proving side. Whether `q` in-circuit ECDSA verifications per fold is a real cost or a rounding error depends on whether the proof system has a signature precompile, and that is unmeasured. If it is cheap, prefix reconciliation was never worth an archive and A was over-engineered. If it is not, C makes every fold expensive and the window in B is what saves it.

### What changes in the specification

Under C or E, token compression changes as follows. The relation's public input `(A, N*)` collapses to a single certified round root `ρ*`, read directly off the anchor seal's `r` field. `VerifyRounds` and the batched round table disappear, and anchored inclusion becomes ordinary Unicity Certificate verification applied at a common round. Check 5's prefix reconciliation branch is deleted, leaving seal reconciliation as the only route, so `h_𝒯` moves from conditionally read to always read. Under E the anchor additionally becomes a commitment to a set of `d` roots and the attestation carries `d` seals, which is the variant the yellowpaper already describes and rejects.

Everything else in the compression design is untouched: re-presentation, the evidence set, reference form, the conserving-edge checks, the expansion frontier.

### Recommendation

**C plus B, and keep `a_r` regardless.**

C removes the accumulator from the leaf path deterministically, at the cost of a distribution change that is a superset of one the accumulator already forces. B restores cheap folding for any wallet that folds within the window, at a cost measured in megabytes inside a component that already exists. Between them they cover every case except folding an attestation older than the window, and that case has a fallback. Neither introduces a role.

Keeping the field is the part not to get wrong. `a_r` costs zero wire bytes because it displaces the backlink, and it cannot be added later: it must be present from genesis for `N = n_r + 1` to hold, and validators keep no persistent chain of past rounds to backfill from. Because the seal carries `(n_r, r, a_r)` and seals are published every round, **any party retaining the seal stream can stand up a full archive service at any future date without asking permission or coordinating with anyone.** So the database and the service are reversible decisions that can be deferred indefinitely, and the field is not. Ship the field, skip the database, and let whoever needs the archive build it from a stream they can already subscribe to.

## Why it is awesome

**It is one field, and it changes what is provable.** A hash chain lets you walk backwards in `O(n)`. An accumulator lets you *jump*, in `O(log n)`, with the same trust assumption and no new one. That is the same upgrade Certificate Transparency made over a naive append-only log, applied to a structure the network is already producing every round.

**It simplifies the security argument rather than complicating it.** "One signature, verified under the trust base you already hold, is the sole root of authority for this entire proof" is dramatically easier to audit than "verify these `F` seals, each under whichever historical trust base it belongs to." Fewer trusted inputs, fewer epochs to reason about, one place to look.

**It is free where it matters and cheap where it doesn't.** Zero bytes on the wire, because it displaces the backlink. Under a kilobyte and a few dozen hashes per round on the BFT Core — a component already doing quorum signature aggregation every round. The benefit lands on every verifier, forever.

**It is a primitive, not a feature.** Token compression is the immediate consumer, but nothing about it is compression-specific: it is a general answer to "was this root ever certified on this chain?", which is a question bridges, light clients, archival services, and auditors all ask.
