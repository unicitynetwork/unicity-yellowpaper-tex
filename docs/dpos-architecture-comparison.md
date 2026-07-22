# DPoS Architecture Comparison: EVM-Partition Contracts vs. Enshrined Staking

Status: draft for review · Date: 2026-07-17

Compares two architectures for Unicity's PoA → DPoS transition of the BFT Core:

- **Architecture A — "EVM-orchestrated"**: staking, delegation, rewards, slashing and
  tokenomics as smart contracts on the enshrined EVM partition; validator sets fed to
  BFT Core by co-signing governance agents. Specified in `docs/dpos-evm-design.md`
  (this repo, branch `evm-pos`).
- **Architecture B — "enshrined"**: staking registry `𝒢` as part of BFT Core's own
  cumulative state; registry transactions (register / bond / unbond / evidence /
  checkpoint) carried in the consensus block payload; deterministic in-protocol
  election; burn-to-bond and mint-to-claim interop with the token layer. Specified as
  yellowpaper modifications on branch `proof-of-stake` (commit `44acd98`).

Standing assumptions, per the review request: the UC-verifier precompile hardening is
done in any case (ignored in complexity); the EVM partition runs **one sequencer node
initially**, distributed later; the EVM partition **exists regardless** of this choice
(exchange integrations and other uses); aggregation-layer nodes are algorithmically
trustless and out of scope.

---

## Executive Summary

The two architectures elect the same committees under the same quorum rule
(top-`c` by bonded stake, `k_e = ⌊⅔·Σb⌋+1`), so their **capital cost of attack is
identical**. They differ in *where the stake ledger lives* and therefore in what else,
besides capital, an attacker or a failure can exploit.

- **Security**: B is strictly stronger in the formal sense. The security of a system
  is the *minimum* over its attack vectors, and A's vector set is a strict superset of
  B's: everything in B, plus the zkEVM proving stack, ~4–6 kLoC of upgradeable
  Solidity, the upgrade-key custody, and (until distributed) a single sequencer whose
  censorship is only neutralized by additional machinery (zk-enforced forced
  inclusion). Each added vector can only lower the minimum. A's *authority* loop is
  still gated by the same ≥⅔ co-signing quorum — the added vectors corrupt the honest
  quorum's *view* of the stake ledger rather than bypass it — but a faithful signature
  over a corrupted ledger is still a corrupted validator set.
- **Liveness of governance**: A's epoch progression requires the conjunction
  BFT Core ∧ EVM partition ∧ prover ∧ agent quorum; B's requires BFT Core alone —
  which must be alive anyway. With one EVM node, A's governance availability is
  bounded by that node's availability. Both degrade safely (epoch extension), but B
  cannot stall for reasons B introduced.
- **Implementation complexity**: comparable in total volume, very differently
  distributed. A spreads ~7 new trust-critical interfaces across five codebases plus
  two new services, but reuses battle-tested Polygon staking logic and keeps BFT Core
  untouched. B concentrates everything into the consensus-critical Go codebase
  (registry state, five transaction validators, election, weighted seal verification —
  the latter already implemented in `bft-go-base`), keeping the *protocol surface*
  markedly smaller; its single heavy new piece is execution-layer token verification
  (`VerifyToken`) in Go for bond evidence. Notably, **both** architectures need a
  `VerifyToken` implementation outside TypeScript anyway (A: in Solidity for
  bridge-out; B: in Go for bonds), and **both** need the native EVM↔token-layer bridge
  regardless, since the EVM partition exists either way — the bridge is orthogonal to
  the staking choice; A merely bundles them and makes the EVM side canonical.
- **Optics**: B presents as textbook enshrined PoS — "the committee is elected by a
  pure function of certified state that anyone can recompute" — with a governance-path
  Nakamoto coefficient equal to the committee quorum from day 1. A, launched today,
  presents as "the validator set is computed on a chain operated by one node, behind
  upgradeable proxies administered by a Foundation key" — defensible technically,
  hard to defend rhetorically. A's optics *advantage* is participation UX:
  standard EVM wallets/explorers for delegation vs. custom tooling for B.

**Bottom line**: B is the stronger *consensus-security* architecture and the cleaner
decentralization story; A is the stronger *programmability and reuse* story. The two
are not mutually exclusive: B enshrines the minimum that consensus security needs
(bond, elect, slash, claim), while the EVM partition — which exists anyway — hosts the
programmable periphery (liquid staking wrappers, exchange rails, treasury, future
tokenomics) *reading* certified registry state rather than *being* the source of
truth. A synthesis sketch is given in §6.

---

## 1. The Two Architectures in One Diagram

```
A (EVM-orchestrated)                        B (enshrined)

 token layer ◄── bridge(39049) ──┐           token layer ◄─ mint-to-claim ─┐
                                 │             │  burn-to-bond             │
 ┌──────────────┐  candidates    │             ▼                           │
 │ EVM partition│──event+MPT──► agents      ┌───────────────────────────┐  │
 │  StakeManager│               │(co-sign)  │ BFT Core                  │  │
 │  Epoch/Seal/ │               ▼           │  state ∋ registry 𝒢       │──┘
 │  Slash/Vault │◄─UC feed── BFT Core       │  payload ∋ registry txs   │
 └──────────────┘  (system tx)              │  elect(𝒢,e) → TB(e+1)     │
   certified per block by BFT Core          └───────────────────────────┘
```

**A**: stake truth lives in contracts; BFT Core certifies the EVM chain per block (zk
validity proof); at each epoch boundary, per-validator agents extract the elected set
(event + Merkle storage proof against the certified state root), deterministically
build the next Unicity Trust Base record, co-sign to ≥⅔ of current stake, and submit
through the existing REST intake. Seals flow back into the contracts (sequencer system
tx, validity-enforced) for reward/participation accounting. UCT's canonical supply
is EVM-native; token-layer UCT is a bridged claim on a vault.

**B**: stake truth lives in BFT Core's own replicated state. Bonding burns an UCT
token on the execution layer against a bond declaration; root validators verify the
burn evidence and credit the registry. The next committee is `elect(𝒢, e)` — a pure
function every validator recomputes; a proposal whose epoch-change record differs from
the recomputation is invalid, so the trust base entry is *computed, not negotiated*.
Withdrawals and rewards are execution-layer mints whose reasons are inclusion
certificates against the certified registry commitment `H(𝒢)` (bound into the trust
base entry's state-summary field). Slashing evidence (conflicting seals E1 /
conflicting votes E2) is mechanically verifiable in-payload. UCT's canonical supply
is execution-layer-native.

A relevant asymmetry of provenance: branch B forked **before** the token-type /
mint-reason framework was specified on `main`. Its then-open item — wire formats for
withdrawal/reward claim mints — is now cheap: the reserved tags 39042/39043
(`MintReasonGenesis`, `MintReasonReward`) and one further tag for withdrawal claims
slot directly into the registry Γ, with verifiers that reuse the SDK's existing trust
base / inclusion-certificate machinery. This closes B's main spec gap at low cost.

---

## 2. Implementation Complexity

### 2.1 Where the new code lands

| | A (EVM-orchestrated) | B (enshrined) |
|---|---|---|
| Codebases touched | 5 (`contracts`*, `uni-evm`, zk guest program, `bft-core`, SDK) + 2 new services (governance agent, standby sequencer ops) | 2 (`bft-core`, SDK) |
| New trust-critical interfaces | ~7: precompile v2 ABI, precompile `0x101`, system-tx validity rule, candidate→TB mapping + agent gossip, forced-inclusion inbox, bridge reason 39049, vault release path | ~3: registry-tx formats (ABNF already drafted), claim mint reasons, checkpoint verifier (separable) |
| Consensus-critical new code | `bft-core`: ~1 line (`Stake==1` relaxation) | `bft-core`: registry state + authenticated-dictionary commitment, 5 tx validators, `elect`, evidence processing, reward accrual; weighted seal verification **already exists** (`RootTrustBaseV1.VerifyQuorumSignatures` sums stakes) |
| Non-consensus new code | ~4–6 kLoC Solidity (Polygon fork + new contracts), agent service, guest-program changes, SDK bridge verifier | SDK claim-reason verifiers (reuse existing UC/trust-base code) |
| Heaviest single item | zk-enforced forced-inclusion + system-tx rules (guest-program/circuit work) | `VerifyToken` in Go (bond evidence validation) |
| Reuse of proven code | High: Polygon StakeManager/ValidatorShare lineage (audited), OZ proxies | Moderate: existing Go trust-base/epoch machinery; election/slashing logic is new but small and standard |

\* the contract suite is a new codebase even though it deploys as genesis allocs.

### 2.2 The honest accounting

Three observations keep the comparison fair:

1. **The `VerifyToken` symmetry.** A needs the full token-provenance walk in
   *Solidity* (vault release / bridge-out); B needs it in *Go* (bond evidence). This
   large, subtle verifier escapes TypeScript in both worlds. It is not a
   differentiator — except that in B it runs inside consensus (a divergence bug halts
   the chain or splits validators), while in A it runs in a contract (a bug loses
   vault funds but not consensus). Severity trades against blast radius.
2. **The bridge is needed in both.** Since the EVM partition ships regardless, the
   native EVM↔token-layer bridge (lock/mint with UC-anchored proofs, burn/release)
   is common-baseline work. A entangles it with consensus security (the vault holds
   the canonical supply backing all token-layer UCT); B leaves it as an ordinary
   asset bridge whose failure does not touch the staking system.
3. **B's DoS surface must be engineered, A's comes free.** Registry transactions in
   the BFT Core payload have no gas market; spam control needs explicit design
   (minimum bond `b_min` bounds bond-tx economics, evidence is deduplicated by
   digest, per-block payload caps for the rest). In A, the EVM gas market prices all
   staking operations natively. This is real but bounded work in B — the transaction
   set is closed and small.

Rough totals: A ≈ B in engineering volume. The decisive difference is *risk
distribution*: A's volume is mostly outside consensus but multiplies deployed
components and inter-component protocols (each a spec, a failure mode, an audit); B's
volume is smaller and self-contained but every line sits in the root chain, and it
makes the BFT Core a (deliberately minimal) transaction processor — a departure from
the "certification only" philosophy of the current design that must be owned
explicitly. B's checkpoint/round-archive machinery is separable and can ship later
without affecting the staking core.

Operationally: A adds two always-on services per validator/network (agent; later,
sequencer redundancy) and an upgrade-governance process for contracts. B adds none.

### 2.3 Time-to-testnet

A can shadow-run against the live PoA set without touching `bft-core` (contracts +
agents in observe mode) — attractive staging. B requires the `bft-core` changes
upfront but has no cross-component integration phase: once the node validates
registry transactions, the whole mechanism exists. Given that A's launch gate
includes the forced-inclusion circuit work (censorship resistance is
launch-blocking with one sequencer), expected time-to-*mainnet* is comparable, and
plausibly shorter for B.

---

## 3. Security Properties

### 3.1 Common core

Both architectures share: chained weak subjectivity (per-epoch trust base records,
hash+signature-linked, next record authorized by ≥⅔ of current stake); the same
election function and quorum rule, hence the same **capital cost of attack**

> C(⅓) = min cost to acquire voting power `> ⅓·Σb` over the elected committee, and
> C(⅔) for outright takeover — identical functions of the stake distribution in A
> and B;

accountable equivocation (two conflicting signatures = self-contained evidence) with
pro-rata slashing of self-bond and delegations; the unbonding invariant
`Δ_ub > evidence window (+ max epoch extension)`; and safe degradation of a stalled
epoch change (incumbent set persists).

### 3.2 The attack-vector inequality

Let `V_B = {≥⅓ stake corruption, bft-core implementation bugs, secp256k1/SHA-256,
Go VerifyToken bug, registry-tx DoS}` be B's vector set. Then

> `V_A = V_B ∪ {zk circuit soundness (SP1 + recursion), ethrex/LEVM correctness,
> Solidity suite correctness, proxy-admin/timelock key custody, agent implementation,
> sequencer censorship (pre-distribution), bridge vault solvency}`

and since achieved security is `min` over vectors, `security(A) ≤ security(B)`, with
equality only if every added vector is costlier to exploit than the cheapest vector
in `V_B`. Several added vectors are *not* obviously costlier: upgrade-key compromise
and contract bugs are historically the dominant loss mode in EVM systems, and zk
soundness bugs, while rare, are catastrophic and non-attributable (no key signed
anything slashable).

The important nuance in A's favor: A's added vectors sit **behind** the co-signing
quorum, not beside it. A corrupted EVM state cannot *push* a trust base into BFT
Core; it can only cause honest agents to faithfully sign a wrong candidate. The MPT
cross-check pins the candidate to certified contract *state*, so the residual risk is
precisely "the contract state itself is wrong" (logic bug, exploited upgrade, fake
stake via a vault/accounting flaw). That is a real and sufficient condition for
validator-set corruption at sub-capital cost — the inequality stands — but it is a
narrower hole than "anyone who controls the EVM controls consensus."

In B, the analogous residual is "the replicated registry logic is wrong," e.g. a
`VerifyToken` divergence admitting a fake bond. Same *category* of risk; smaller code
base, no upgrade keys, no second execution environment, and any exploit requires
passing validation by *every* root validator independently rather than by one
sequencer plus a proof system.

### 3.3 Liveness of governance (availability math)

Let `p_X` be per-epoch availability of subsystem X (probability the epoch change
completes in its window). Then, to first order:

> **A**: `p_gov = p_bft · p_evm · p_prover · p_agents` — a conjunction of four
> subsystems; with a single sequencer node, `p_evm` is the availability of one
> machine and its operator, and dominates.
> **B**: `p_gov = p_bft` — governance lives inside the very system whose liveness is
> already assumed.

Both fail *safe* (epoch extension: the incumbent set persists, no wrong set
activates). But extension is not costless: every extension epoch prolongs exposure to
a set that stakers may be trying to vote out, and stretches the effective unbonding
constraint (`Δ_ub` must exceed the *maximum tolerated* extension). Under A the
extension trigger includes failures Unicity did not otherwise have (EVM node down,
prover down, agent quorum partition); under B it is exactly the failure of consensus
itself, which extension cannot mask anyway.

Censorship: in A, until sequencer distribution, inclusion of staking/evidence
transactions has Nakamoto coefficient 1; restoring censorship resistance requires the
zk-enforced forced-inclusion inbox — additional consensus-critical machinery whose
own correctness joins `V_A`. In B, inclusion is by BFT Core leaders, rotating over
the committee; censorship resistance equals that of consensus itself (a censoring
leader is routed around next round; a censoring *quorum* is already the ≥⅓
corruption case).

### 3.4 Supply integrity

- **A**: canonical UCT supply is EVM-native; conservation is enforced by zk-proved
  EVM semantics (strong) *plus* vault solvency for everything token-layer-side
  (`Σ token-layer UCT = vault balance`, invariant of the bridge). Supply security
  inherits the contract/upgrade/zk vector set. A vault compromise is a loss event for
  the *currency*, not just for stakers.
- **B**: canonical supply is execution-layer-native; conservation =
  `genesis + Σ claims`, each claim a consensus-verified mint against the certified
  registry (double claims collapse to double spends of the same token identifier —
  rejected by the unicity mechanism itself, an elegant reuse). No custody
  concentration exists; there is no single contract whose compromise touches all
  bridged value. The (still needed) EVM bridge in B carries only the value users
  choose to move onto the EVM partition, not the staking system or the currency root.

### 3.5 Reward/participation accounting

A imports seal signer-sets into contracts via a validity-enforced system transaction
— correct under the zk assumption, but an import nonetheless. B computes rewards
in-protocol from the signer sets it produced itself; there is no import, no relayer,
and no extra assumption. Slashing evidence paths are equivalent (permissionless
submission with bounty in both).

---

## 4. Optics of Decentralization

Optics are about what a skeptical third party can *verify* and what they will *say*.

**Verifiability.** B's election is a pure function of certified state:
`TB(e+1) = elect(𝒢, e)` where `H(𝒢)` is committed in the trust base entry itself.
Anyone with the trust base chain can recompute every committee ever elected —
"don't trust, recompute" — and the ABNF already specifies the wire formats. A is
verifiable too, but the verification story is a chain: replay EVM blocks (or trust
the zk verifier), read contract storage, check the agent mapping, check the
co-signatures — each step explainable, none of it one sentence.

**Nakamoto coefficients on the governance path** (day-1, single EVM node):

| Path | A | B |
|---|---|---|
| Stake-ledger *safety* | quorum of root committee **and** proxy-admin threshold (a 1-of-2 conjunction of failure points: min(quorum, upgrade keys)) | quorum of root committee |
| Staking-tx *inclusion* | 1 (sequencer) until forced inbox / distribution | leader rotation over committee |
| Epoch-change *liveness* | min(committee, 1 EVM node, prover) | committee |

A's day-1 answer to "who can freeze or steer validator-set evolution?" includes a
single machine and a multisig; B's answer is "the committee, which is the thing being
measured." The forced-inclusion inbox and later sequencer distribution repair A's
inclusion row, but that is a roadmap promise at launch — and "the staking chain is
run by one node, but there's a zk-enforced escape hatch" is a two-paragraph rebuttal
in a debate that allows one sentence.

**Where A's optics win: participation.** Delegating via any EVM wallet against a
verified contract, watching stake and rewards in a standard explorer, exchanges
integrating staking with tooling they already run — that is a *breadth*-of-
decentralization argument (more, smaller delegators) with real weight, and it aligns
with the plan to use the EVM partition for exchange integrations anyway. B's
equivalents (burn-to-bond transactions, registry claims) need custom wallet and
explorer support that must be built and adopted before delegation is comparably
accessible.

**Enshrinement as a statement.** "Staking is part of the protocol, not an app" reads
as commitment: parameters change by protocol release (visible, forkable), not by
timelocked admin transaction. Conversely A keeps tokenomics *iterable* — a genuine
engineering virtue that reads, optically, as *mutable*.

---

## 5. Scorecard

| Criterion | A: EVM-orchestrated | B: enshrined |
|---|---|---|
| Capital cost of attack | identical | identical |
| Non-capital attack vectors | strict superset (contracts, zk, keys, sequencer) | minimal (consensus code itself) |
| Governance liveness | product of 4 subsystems; 1-node EVM dominates | = consensus liveness |
| Censorship resistance (day 1) | NC = 1 until forced inbox ships | = consensus |
| Supply integrity | zk-EVM + vault solvency | consensus-verified claims; no custody root |
| Consensus-code delta | ~1 line | substantial (registry, election, evidence) |
| Total new code / components | more, spread over 5 codebases + 2 services | less, concentrated in bft-core + SDK |
| Reuse of audited logic | high (Polygon lineage) | low-moderate |
| BFT Core scope | stays pure certification | becomes minimal tx processor |
| Tokenomics iterability | contract upgrade (fast, key-gated) | protocol release (slow, fork-visible) |
| Participation UX | standard EVM tooling | custom tooling required |
| Verifiability story | multi-step, explainable | one sentence, recomputable |
| Spec status | full design doc (this repo) | yellowpaper diff; claim formats now cheap via main's mint-reason framework |

---

## 6. Synthesis (recommendation sketch)

The comparison suggests a division of labor rather than a winner-take-all choice:

1. **Enshrine the consensus-critical minimum (B)**: bond, delegate, elect, slash,
   claim — in BFT Core, as specified on `proof-of-stake`, completed with claim
   mint-reason formats from `main`'s token-type framework (tags 39042/39043 + a
   withdrawal-claim tag). The validator set of the root of trust then depends on
   nothing outside the root of trust and the capital behind it.
2. **Keep the EVM partition as the programmable periphery (from A)**: it exists
   anyway. Give it read access to certified registry state (the UC precompile +
   registry inclusion certificates make `𝒢` provable on-chain) and build the
   flexible layer there: liquid-staking wrappers, exchange integration rails,
   delegation front-ends that compose bond transactions, treasury and future
   tokenomics experiments. None of these can corrupt the committee, because none of
   them are the source of truth.
3. **Reuse A's design work regardless**: the native bridge (39049), the precompile
   v2 / signer-bitmap extension, FeeCollector/coinbase repair, and the availability
   roadmap for the EVM partition all remain wanted — they simply stop being on the
   consensus-critical path.

This captures B's security minimum and optics, A's programmability and UX, and
retires the two least comfortable properties of A alone: the 1-node partition inside
the governance loop, and the upgrade key with (indirect) authority over the validator
set.
