# Unicity DPoS via the Enshrined EVM Partition — High-Level Design

Status: **draft for review** · Scope: BFT Core root validators · Date: 2026-07-17

---

## 1. Introduction and Scope

This document designs the transition of Unicity's BFT Core (root chain) from Proof of
Authority to **delegated Proof of Stake (DPoS)**, using the enshrined EVM partition
(standard partition type `st = 8`, `platform.tex`) as the programmable substrate for the
validator registry, staking, delegation, rewards, slashing, and tokenomics of the native
currency **UCT**.

### 1.1 The key architectural insight

The staking contracts live on a chain that is **itself certified per block by the very
root chain being governed**. Every EVM block is proven valid with a zk proof (SP1) and
certified by a Unicity Certificate (UC) before the next block is produced. This inverts
the usual L1-staking-for-L2 topology (Polygon-on-Ethereum) and deletes its hardest
problems:

- The contracts never need to *verify the honesty of the root chain* the way Polygon's
  `StakeManager` verifies checkpoint signatures on Ethereum — the EVM partition's own
  state is only final because the root chain certified it.
- The Unicity Seal verification builtin (precompile at `0x…0100`) is needed for exactly
  three things: (a) importing per-round **signer participation** (who co-signed each
  seal — the input to rewards and downtime accounting), (b) verifying **slashing
  evidence** (conflicting signatures), and (c) verifying **bridge-out proofs** (token-
  layer burns presented to the native vault).
- Polygon's most complex machinery (checkpoint signature aggregation on L1,
  StateSender/StateReceiver, the Heimdall layer) is not ported at all.

### 1.2 In scope / out of scope

**In scope:** DPoS for the **BFT Core root validator set** only; UCT genesis +
emission on the EVM partition; a Polygon-PoS-derived contract suite; the native bridge
between the EVM partition and the token (execution) layer; required changes to
`bft-core`, `uni-evm`, `state-transition-sdk-js`, and the yellowpaper; an availability
roadmap for the EVM partition; security analysis.

**Out of scope (this iteration):** partition/shard validator assignment (stays
PoA/manual; the extension path is noted in §9.5 — the Governance chapter's Validator
Assignment Record has the same `{ν, b_ν}, k_e` shape, so `EpochManager` generalizes
naturally); migration of the existing PoW UCT chain; BLS accountable-subgroup
multisignatures (roadmap note only, §11.12); liquid staking.

---

## 2. Background: Current State

Facts below are verified against the repositories checked out beside this document.

### 2.1 BFT Core (`bft-core`, Go; core types in `bft-go-base` v1.1.1)

- **The trust base is already stake-shaped.** `RootTrustBaseV1`
  (`bft-go-base/types/root_trust_base.go`) carries `Epoch`, `EpochStart` (activation
  round), `RootNodes []*NodeInfo`, `QuorumThreshold`, `PreviousEntryHash`, and
  `Signatures` — the signatures of the **previous** epoch's validators, forming a
  hash+signature chain of trust base records exactly as specified in the yellowpaper
  (`bft.tex`, Table "Unicity Trust Base Record"). `NodeInfo` has a `Stake uint64`
  field, and `VerifyQuorumSignatures` already **sums signer stakes** against
  `QuorumThreshold` (= 2/3·total + 1 by default). PoA is enforced by a single line:
  `NodeInfo.IsValid()` requires `Stake == 1` (`root_trust_base.go:149`).
- **Epoch machinery is live.** `TrustBaseStore` stores one trust base per epoch and
  validates chaining via `Verify(prev)`; `ConsensusManager.updateTrustBase()` activates
  a stored record when the current round reaches its `EpochStart` and refreshes the
  leader selector.
- **Config ingestion is external.** Startup JSON files plus runtime REST:
  `PUT /api/v1/trustbases` → `TrustBaseStore.Store` and
  `PUT /api/v1/configurations` → `Orchestration.AddShardConfig`
  (`cli/ubft/cmd/root_node.go:254-256`). This is the seam where the DPoS-derived feed
  replaces the PoA feed — **no consensus-code change is needed for intake**.
- Consensus is a HotStuff-derived protocol ("ABDRC"); leader selection
  (`rootchain/consensus/leader/reputation.go`, `pickLeader()`) is uniform over
  validators — the natural hook for optional stake weighting.
- Per-round fee/statistics accounting already flows to the root chain
  (`InputRecord.SumOfEarnedFees`, `TechnicalRecord.FeeHash/StatHash`).

### 2.2 EVM partition (`uni-evm`, Rust zkEVM on ethrex)

- Single sequencer. Per block: mempool → `BlockProducer` → `ProofCoordinator` (SP1
  compressed proof, or LightClient witness) → `BftCommitter` sends a CBOR
  `BlockCertificationRequest` to BFT Core over libp2p → BFT Core verifies the zk proof
  and returns the UC → block finalized. **Per-block UC finality; no reorgs.**
- **Precompile `0x…0100`**: `verifyUnicityCertificate(bytes ucCbor) → (bool valid,
  bytes32 stateHash, uint64 roundNumber)`, gas `3000 + 6/byte`
  (`crates/bft-precompile/src/precompile.rs`). **Caveat: quorum-signature verification
  is currently a stub** — it counts trust-base node ids present in the seal's signature
  map without verifying the secp256k1 signatures (`trust_base.rs`, explicit TODOs). The
  JS SDK contains a correct reference implementation
  (`UnicitySealQuorumSignaturesVerificationRule.ts`). Hardening this is a **P0
  prerequisite** for everything in this document (§6.3).
- Trust base is injected node-side by `TrustBaseUpdater` (polls BFT Core REST, 1 h
  refresh).
- Plain EIP-1559 gas; 30 M block gas limit; 1 gwei base fee; **coinbase =
  `address(0)`** — fees currently vanish. Genesis (`genesis.json`, chainId 3) has two
  dev accounts and **no predeployed contracts** (ethrex genesis supports `code` allocs,
  so predeploys are available).

### 2.3 Token (execution) layer (`state-transition-sdk-js` + yellowpaper)

- Token genesis `D_mint = (α, pred′, salt, ty, reason, aux′)`; token types
  `D_ty = (ty, RT, ParseAux, VerifyIssuance, meta)`; mint reasons are tagged CBOR
  items dispatched through a verifier registry Γ; **fail-shut** on mainnet
  (`execution-layer.tex`, "Token Types and Mint Authorization").
- Reserved mint-reason tags **39042 MintReasonGenesis** ("native-coin genesis
  allocation") and **39043 MintReasonReward** ("validator reward issuance") have
  unspecified bodies (`appendix-token-types.tex:83-84`); **39048 BridgeMintReason** is
  fully specified for external-chain bridging (`appendix-bridging.tex`); tag **39049 is
  unused** and claimed by this design (§8).
- The SDK's pluggable framework — `MintTransaction` (tag 39041) with a `justification`
  field, `MintJustificationVerifierService` dispatching by CBOR tag, `BurnPredicate`
  (type 0x02) with a `reason` field, and real UC/seal/trust-base verification under
  `src/api/bft/` — is exactly the plug-in point for the native bridge verifier.

---

## 3. Architecture Overview

```
                          ┌────────────────────────────────────────────┐
                          │                BFT Core (root chain)       │
                          │  TrustBaseStore ── epoch e trust base      │
                          │  ▲ PUT /api/v1/trustbases                  │
                          │  │            certifies every EVM block    │
                          │  │            (zk proof verified) ────────┐│
                          └──┼────────────────────────────────────────┼┘
              co-signed      │                                        │ UC (seal, epoch,
              TB(e+1)        │                                        │  signer map)
                          ┌──┴──────────────┐          system tx      ▼
                          │ governance      │        ┌────────────────────────────┐
                          │ agents (one per │◄───────┤  EVM partition (chainId 3) │
                          │ root validator) │ event+ │  StakeManager ValidatorShare│
                          └─────────────────┘ MPT    │  EpochManager SealRegistry │
                                              proof  │  Rewards/Emission Slashing │
                                                     │  FeeCollector NativeVault  │
                                                     └──────────┬─────────────────┘
                                                                │ lock/mint, burn/release
                                                                ▼
                                                     Token (execution) layer
```

The control loop, one epoch `e → e+1`:

1. Anyone stakes or delegates UCT in the contracts; every EVM block is certified by
   BFT Core under the epoch-`e` trust base.
2. At **snapshot round `S_e`** (BFT round numbers, read from imported seals, are the
   canonical clock — §4.3), `EpochManager.finalizeEpoch()` selects the epoch-`e+1`
   validator set (top-N by total stake meeting minimum self-stake), computes the quorum
   threshold `k_{e+1} = ⌊2Σb/3⌋ + 1`, emits `TrustBaseCandidate(e+1, …)` and writes its
   canonical hash to a well-known storage slot.
3. Each root validator runs a **governance agent** (§5). The agent reads the candidate
   from its own UC-anchored view of the EVM chain, cross-checks it with an MPT storage
   proof against the certified state root, deterministically constructs
   `RootTrustBaseV1(e+1)`, signs it, and exchanges signatures with the other agents.
4. Once signatures representing **≥ 2/3 of epoch-`e` stake** are collected (the
   existing chaining rule), any agent submits the record via `PUT /api/v1/trustbases`
   to all root nodes. `TrustBaseStore.Store` validates chaining as it already does.
5. At round `A_e = EpochStart(e+1)`, `ConsensusManager.updateTrustBase()` activates the
   new set. The loop closes: epoch-`e+1` certification of the EVM chain is now
   performed by the set that the EVM chain itself computed.
6. **Reverse flow:** each block, the sequencer injects a system transaction feeding the
   previous block's UC into `SealRegistry` (§6); the per-round signer maps drive reward
   distribution and downtime slashing.

If the EVM partition stalls or no candidate reaches quorum in time, **the epoch-`e`
trust base simply persists** (this is current `bft-core` behavior — activation only
happens when a stored record's `EpochStart` arrives). This *epoch extension rule* is
the system's liveness backstop (§5.4, §11.1).

---

## 4. Contract Suite

Solidity contracts, adapted from Polygon PoS (`maticnetwork/contracts` staking suite),
deployed as **genesis predeploys behind upgradeable proxies** at reserved addresses
(`0x…F000` range suggested). Reuse/rewrite matrix in Appendix E.

| Contract | Polygon ancestor | Responsibility |
|---|---|---|
| `StakeManager` | `StakeManager` | Validator lifecycle, self-stake, unbonding, key rotation |
| `ValidatorShare` (per validator) | `ValidatorShare` | Delegation with share accounting, commission |
| `EpochManager` | *(new; replaces checkpoints)* | Epoch clock, set finalization, trust base candidate |
| `SealRegistry` | *(new)* | Imports certified seals; per-round signer bitmaps |
| `RewardsDistributor` + `EmissionPool` | `StakingInfo` (reworked) | Emission release, participation-weighted rewards |
| `SlashingManager` | `SlashingManager` (reworked) | Double-sign and downtime slashing, jailing |
| `FeeCollector` | *(new)* | Coinbase target; burn/reward fee split |
| `UnicityGovernance` | `Governance`/`Registry` | Parameter registry + timelock |
| `NativeVault` | *(new; per appendix-bridging)* | Native bridge to the token layer (§8) |

### 4.1 StakeManager

State per validator id:

```solidity
struct Validator {
    address owner;             // funds/admin key (EVM account)
    bytes   consensusPubKey;   // 33-byte compressed secp256k1 (BFT signing key)
    string  nodeId;            // libp2p peer id, derived from consensusPubKey
    string  networkAddress;    // multiaddr
    uint256 selfStake;
    uint256 delegatedStake;    // mirrored from ValidatorShare
    uint16  commissionBps;
    Status  status;            // Active | Unbonding | Unstaked | Jailed | Slashed
    uint64  activationEpoch;
    uint64  deactivationEpoch;
}
```

Functions: `stake(pubkey, nodeId, netAddr, commissionBps) payable`,
`stakeMore() payable`, `unstake()` (starts unbonding; validator leaves the candidate
set at the next snapshot), `claimUnstaked()` (after the unbonding period, §7.4),
`updateSigner(newPubkey)` (key rotation, effective next epoch), `updateCommission`
(rate-limited), `updateNetworkAddress`.

**Deltas vs Polygon:** staking is **native UCT (`payable`)**, not ERC-20
`transferFrom`; `nodeId`/`networkAddress` added because `NodeInfo` in the trust base
needs them; all Ethereum-checkpoint logic removed; owner key ≠ consensus key is
enforced (the consensus key never controls funds — §11.11).

### 4.2 ValidatorShare (delegation)

Reused nearly verbatim from Polygon: per-validator delegation vault with
exchange-rate share accounting (`buyVoucher`/`sellVoucher`), commission skimmed to the
validator owner, delegator unbonding queue with the same unbonding period as
self-stake. Delta: native UCT transfers; reward inflow comes from
`RewardsDistributor` (§4.5) instead of Polygon's checkpoint reward path.

### 4.3 EpochManager

Conceptually replaces Polygon's checkpoint mechanism. The **epoch clock is the BFT Core
round number** taken from the latest imported seal (`SealRegistry.latestRound()`);
since every EVM block is 1:1 certified, this clock is fresh to within one block.

State: current epoch `e`, `epochLength L` (in root rounds), snapshot round
`S_e`, activation round `A_e = S_e + Δ`, the finalized candidate set.

`finalizeEpoch()` — callable by **anyone** once `latestRound() ≥ S_e`:

1. Select up to `maxValidators` active validators by total stake (self + delegated),
   subject to `minSelfStake` and not-jailed.
2. Compute `k_{e+1} = ⌊2·Σstake/3⌋ + 1` (mirrors `bft-go-base` `NewTrustBase`).
3. Emit `TrustBaseCandidate(epoch e+1, epochStartRound A_e, entries[], quorum, prevHash)`
   where `entries[i] = (nodeId, consensusPubKey, stake)` sorted by `nodeId`, and write
   `keccak256(canonicalCbor(candidate))` to storage slot `TRUST_BASE_CANDIDATE_SLOT`
   (fixed, documented — the MPT-proof anchor for governance agents).
4. Freeze the stake snapshot: stake changes after `S_e` count for epoch `e+2`.

The candidate's `prevHash` field carries the hash of the previous
`RootTrustBaseV1` entry so the produced record chains correctly (Appendix A gives the
exact field mapping).

### 4.4 SealRegistry

`submitSeal(bytes ucCbor)`:

- Calls precompile `0x…0100` (v2 ABI, §6.3) → `(valid, stateHash, round, epoch,
  signerBitmap)`; reverts unless valid and `round` is new.
- Stores `round → signerBitmap` (bitmap ordered by the epoch's trust-base validator
  list) and updates per-epoch, per-validator participation counters (compacted; raw
  bitmaps pruned after the evidence window).

Fed primarily by a **sequencer system transaction** each block carrying the *previous*
block's UC (§6.1); a **permissionless fallback** path (with a small gas refund from
`FeeCollector`) guarantees liveness of the data feed and of slashing evidence even
against a faulty or hostile sequencer.

### 4.5 RewardsDistributor + EmissionPool

**No native mint opcode is added to the EVM.** Emission = scheduled release from
`EmissionPool`, a contract holding the entire staking-emission allocation from genesis
(§7.2). Rationale: keeps ethrex balance semantics untouched; total supply is fixed at
genesis and enforceable by inspection.

Per epoch, at first `SealRegistry` write of the new epoch (or lazily on claim):

```
epochReward = emission(e) + FeeCollector.epochPot(e)
validatorReward_v = epochReward · stake_v/Σstake · participation_v
```

where `participation_v = signedRounds_v / totalRounds` in epoch `e` (from
`SealRegistry`), with a floor `participation_v ≥ p_min` (default 0.9) below which the
reward is zero (softer than slashing; §4.6 handles persistent downtime). Commission is
skimmed to the validator owner; the remainder accrues to the `ValidatorShare` exchange
rate (delegators earn pro rata, Polygon-style).

### 4.6 SlashingManager

Only **on-chain-provable** offenses; no committee/oracle (delta vs Polygon, whose
slashing needs Heimdall consensus):

- **Double-signing.** Evidence = two BFT vote/seal signature payloads for the same
  round with different hashes, both verifying under the same `consensusPubKey`.
  Verified via precompile `0x…0101` (§6.3), which encapsulates the canonical
  vote-payload hashing (Appendix B) so Solidity never re-implements CBOR. Penalty:
  slash `slashFractionDoubleSign` (default 5%) of total stake (self + delegated),
  jail; repeat → tombstone.
- **Downtime.** `participation_v < d_min` (default 0.5) over a full window of `W`
  rounds, computed from `SealRegistry` counters — provable by anyone, no evidence
  submission needed beyond the seals already imported. Penalty:
  `slashFractionDowntime` (default 0.1%), temporary jail for `jailPeriod` epochs.

Slashed amounts: 50% burned, 50% to the epoch reward pot (parameter). A successful
evidence submitter receives a bounty from the slashed amount (incentivizes
permissionless enforcement).

### 4.7 FeeCollector

Set as the block `coinbase` (§9.2). Splits accumulated fees per epoch:
`burnBps` (default 50%) to `0x…dEaD`, remainder to `RewardsDistributor.epochPot`.
Also funds the `submitSeal` gas refund.

### 4.8 UnicityGovernance

Parameter registry (every tunable in Appendix D, each with hard min/max bounds) behind
a timelock (default 7 days). Initially controlled by a Foundation multisig; roadmap:
stake-weighted on-chain voting. Also owns `ProxyAdmin` for contract upgrades
(timelocked; upgrade of `NativeVault` additionally constrained by the bridge's
config-hash pinning, §8.5).

### 4.9 Licensing note

Polygon's staking contracts are predominantly MIT-licensed, but the repo has mixed
headers; a file-by-file license audit (Appendix E) is a **pre-fork checklist item**. If
any GPL-3.0 file is pulled in, the derived suite must be GPL — acceptable for on-chain
code, but it must be a conscious decision.

---

## 5. Data Flow A: EVM Staking State → BFT Core Trust Base

**Chosen mechanism: per-root-validator governance agents + the existing
signature-chaining REST intake.** Rationale: requires zero changes to consensus code;
the ≥2/3-of-previous-epoch signature rule *is already* the trust anchor for trust base
records, so no relayer or oracle is trusted; MPT proofs are defense-in-depth inside the
agent rather than a new protocol.

### 5.1 The governance agent

A small sidecar service (new; lives in the `bft-core` repo) run by each root
validator, holding (a) the validator's trust-base signing key, (b) a UC-anchored view
of the EVM chain — either a full `uni-evm` node or a light client that verifies UCs
the validator itself co-signed.

On observing `TrustBaseCandidate(e+1)`:

1. Read the candidate from the event; verify it against an **MPT storage proof** of
   `TRUST_BASE_CANDIDATE_SLOT` under the UC-certified state root of the same block.
2. Deterministically construct `RootTrustBaseV1{Epoch: e+1, EpochStart: A_e,
   RootNodes: [{NodeID, SigKey, Stake}…], QuorumThreshold: k_{e+1},
   PreviousEntryHash: H(TB_e)}` per the canonical mapping in Appendix A.
3. Sign it; gossip the signature to the other agents (libp2p topic or simple REST
   exchange between agents — implementation detail).
4. When signatures of epoch-`e` validators holding **≥ 2/3 of epoch-`e` stake** are
   assembled, any agent submits the completed record to every root node via
   `PUT /api/v1/trustbases`. `TrustBaseStore.Store` re-validates chaining
   (`Verify(prev)`) exactly as today.

Determinism of step 2 means all honest agents produce byte-identical records, so
signatures compose without coordination beyond gossip.

### 5.2 Timing

- `epochLength L` ≈ 1 day of root rounds (governance-tunable).
- Snapshot/finalize at `S_e`; activation at `A_e = S_e + Δ` with `Δ` ≈ 1–2 hours of
  rounds: margin for the `finalizeEpoch()` transaction, agent verification, signature
  gossip, and submission.
- Stake operations after `S_e` take effect in epoch `e+2`.

### 5.3 Bootstrap

Genesis trust base (epoch 0) is the current PoA set with `Stake = 1`. The first DPoS
epoch is produced by the same flow: the PoA validators' agents sign `TB(1)` derived
from the contracts. From then on the induction of §11.1 applies. During a
transitional period the Foundation multisig can veto candidates via
`UnicityGovernance` (§11.7).

### 5.4 Fallback: epoch extension

If no `TB(e+1)` is stored by round `A_e` (EVM stall, prover failure, no agent
quorum), the epoch-`e` trust base **persists** — `updateTrustBase()` only switches
when a stored record's `EpochStart` arrives, so this is existing behavior, now
promoted to a documented rule: a late candidate is re-issued with a fresh
`EpochStart`. Consequence: the unbonding period must exceed the maximum tolerated
extension (§11.4).

---

## 6. Data Flow B: BFT Core → EVM Contracts

### 6.1 Primary feed: sequencer system transaction

The sequencer injects, as the **first transaction of every block**, a system tx (from
a reserved system address, zero gas price) calling
`SealRegistry.submitSeal(prevBlockUC)`. The sequencer already holds this UC — it is
the certification response that finalized the previous block.

**Enforced by validity, not trust:** the zk guest program is extended to require the
presence and well-formedness of this system tx; a block omitting it is unprovable and
therefore uncertifiable. Omission is a liveness fault of the sequencer, never a data
gap the contracts silently tolerate.

### 6.2 Backup feed: permissionless submission

Anyone may call `submitSeal` with any valid, not-yet-imported UC (small gas refund
from `FeeCollector`). This keeps reward accounting and, critically, **slashing
evidence** live even if the sequencer misbehaves; combined with forced inclusion
(§10, stage 1) the evidence path has no trusted party.

### 6.3 Precompile work (in `uni-evm/crates/bft-precompile`)

1. **P0 — harden `0x…0100`.** Implement real secp256k1 signature verification of the
   seal's signature map against the trust base (port the logic of the JS SDK's
   `UnicitySealQuorumSignaturesVerificationRule`). Until this lands, the precompile
   accepts any well-formed UC and *nothing* in this design is safe. Independent of
   DPoS; ship first.
2. **v2 ABI.** Extend output to
   `(bool valid, bytes32 stateHash, uint64 roundNumber, uint64 epoch, bytes signerBitmap)`
   with the bitmap ordered by the trust base's validator list — `SealRegistry` gets
   participation for free, without parsing CBOR in Solidity.
3. **New precompile `0x…0101` `verifyValidatorSignature(bytes payload, bytes sig,
   bytes pubkey) → (bool ok, bytes32 payloadHash, uint64 round, bytes32 votedHash)`**:
   verifies one consensus signature over the canonical BFT vote/seal signing payload
   and returns the parsed `(round, votedHash)` binding — the primitive
   `SlashingManager` needs for double-sign evidence (Appendix B).
4. **Trust base source.** Today the node injects the trust base from BFT Core REST
   (1 h poll). Transitional design keeps node injection; once DPoS is authoritative
   the node sources it from its own chain's `EpochManager` state (self-consistent,
   §11.1), with REST as cross-check.

---

## 7. Tokenomics

### 7.1 Principles

UCT is the **native gas token of the EVM partition**, and the EVM partition holds the
**single canonical supply**. Every other representation — including token-layer UCT —
is a bridged claim on vault-locked native UCT (§8). Total supply is fixed at genesis;
"emission" is scheduled release from a genesis-allocated pool, not minting (§4.5).

### 7.2 Genesis allocation (placeholder — explicit governance decision)

Total supply **1,000,000,000 UCT** (placeholder):

| Bucket | Share | Notes |
|---|---|---|
| EmissionPool (staking rewards) | 40% | released per §7.3, pool-capped |
| Foundation | 20% | timelocked vesting |
| Ecosystem / community | 15% | grants, incentives |
| Backers | 15% | vesting |
| Validator bootstrap + liquidity | 10% | initial stake, market ops |

Recorded in `genesis.json` allocs; each bucket is a contract (vesting/pool), not an
EOA.

### 7.3 Emission schedule

Exponential decay: year-`y` emission `E_y = E_0 · r^y`, `r = 0.85`, `E_0` sized so
that at a 30% staked ratio the staking APR ≈ 10% in year 0. Per-epoch emission
`E_y / epochsPerYear`, hard-capped by the `EmissionPool` balance. `E_0` and `r`
tunable via governance within Appendix D bounds.

### 7.4 Parameters (defaults; full table in Appendix D)

- `minSelfStake` 100,000 UCT; `minDelegation` 100 UCT.
- `maxValidators`: 25 at launch → 100 (governance-raised).
- Commission 0–100%, change rate-limited (≤ 1 pp/epoch, Polygon-style).
- **Unbonding period 21 days**, with the hard constraint
  `unbonding > evidenceWindow + downtimeWindow + maxEpochExtension` (§11.4).
- Optional per-validator stake cap (capture resistance, §11.7).

### 7.5 Fees

Coinbase → `FeeCollector`; default split 50% burn / 50% epoch reward pot. The
existing `sum_of_earned_fees` reporting to BFT Core stays informational this phase.

---

## 8. Native Bridge: EVM Partition ↔ Token Layer

Reuses the yellowpaper's bridging framework (`sec:bridged-assets`,
`appendix-bridging.tex`) with the external-chain machinery removed: the token-layer
verifier already trusts the Unicity trust base, so **no external light client, no
finality committee, and no zk proof of Unicity state** are needed.

### 8.1 Mint reason: new tag `39049 NativeBridgeMintReason`

A **new tag**, not a reuse of 39048. Rationale: 39048's verifier relation is pinned to
*external-chain finality proofs* (`app:bridging-finality`); the native verifier
consumes a *Unicity UC + EVM receipt proof* — a different relation deserves a distinct
Γ dispatch tag and leaves the 39048 spec untouched. Registry entry: "39049 ·
NativeBridgeMintReason · specified · backing by lock on an enshrined EVM partition."

Body (canonical CBOR, full definition in Appendix C):

```
39049([ ucCbor,          ; UC certifying the block containing the lock
        blockHeader,     ; EVM block header (RLP)
        receiptProof,    ; MPT inclusion proof of the lock receipt
        lockRecord ])    ; (vaultAddr, tokenId, hRecipient, amount, nonce)
```

### 8.2 Token type

A UTS-1 specialization (mirroring the bridged-asset variant at
`appendix-token-types.tex:431`): `RT = {39049, 39044}` (native-bridge issuance +
split), issuance parameter `h_cfg = H_cfg(chainId = 3, partitionId, vaultAddr,
assetId = NATIVE_UCT, ty, aid, domain separators)`; `ty` content-addressed over the
frozen definition. The same pattern instantiates for any ERC-20 on the EVM partition
(per-asset `h_cfg`).

### 8.3 Bridge-in (EVM → token layer): lock and mint

1. User picks recipient predicate `pred′₀` and salt off-chain (token id
   `id = H(salt, α)`, `h_rcpt = H(CBOR(pred′₀))` — same as 39048 flow).
2. `NativeVault.lockForBridge(id, h_rcpt) payable` escrows native UCT (or, for
   ERC-20s, `transferFrom`) and emits `Locked(id, h_rcpt, amount, nonce)` with a
   strictly monotone nonce; the vault records `lockDigest[id]`.
3. User mints on the token layer with reason 39049. The verifier (new, in the SDK):
   - verifies the UC against the Unicity trust base (existing
     `src/api/bft` machinery — the trust base is the *only* trust root);
   - **binds the EVM block header to the UC**: checks that the header commitment
     matches the certified input record per the EVM partition's consistency-proof
     binding (`IR.h` ↔ block hash / state root) — this is the one nontrivial link and
     is specified normatively in Appendix C.1;
   - verifies the receipt MPT proof against `header.receiptsRoot`, decodes the
     `Locked` event, checks `(vaultAddr, assetId)` against `h_cfg`, and matches
     `(id, h_rcpt, amount)` to the genesis being minted;
   - enforces no-double-mint: `id` is unique per lock by construction (the vault
     rejects a reused `id`), and the token layer's own uniqueness of `id` completes
     the guarantee.

No finality wait: per-block UC finality means a certified lock is irreversible
(`no-reorged-lock` holds trivially).

### 8.4 Bridge-out (token layer → EVM): burn and release

This is where "**no zk needed**" applies, for two reasons stated in the yellowpaper's
own terms: (a) the vault can verify Unicity Seals natively via precompile `0x…0100`,
and (b) gas limits on our own partition are controllable, so the bounded
`VerifyToken` walk can run **directly in Solidity** instead of inside a SNARK.

1. Token holder transfers the token to the **burn predicate** (type 0x02) with reason
   `(evmRecipient, amount, nonce)` and obtains the certified burn (final once
   BFT-certified).
2. Holder (or anyone) calls `NativeVault.release(tokenProvenance, proofs)`:
   - every certified transition in the provenance is checked against its UC via
     `0x…0100` (trust-base epochs handled via the allow-listed trust-base chain, as in
     `app:bridging-settlement`);
   - the full `VerifyToken` walk (genesis → … → burn), including split-reason value
     conservation, runs on-chain over the **bounded history** (`maxHistoryLen`
     parameter; §11.9);
   - the burn reason's `(evmRecipient, amount)` is honored; a **nullifier**
     `η = H(NUL_DOMAIN, h_cfg, burnTxId)` recorded in a vault mapping prevents
     double-release (simplification of `app:bridging-nullifier`'s accumulator — a
     plain mapping suffices on our own chain where storage is cheap and the vault is
     the only writer);
   - vault pays out native UCT.
3. **SNARK path as optimization only:** for histories exceeding `maxHistoryLen`, the
   holder first compresses history on the token layer (history-compression reason) or
   uses the batch SNARK relation of `app:bridging-relation`. Not required at launch.

### 8.5 Security invariants (mapping from `app:bridging-security`)

| Invariant | Native-setting argument |
|---|---|
| No-mint-without-lock | mint reason verifies certified `Locked` receipt under UC |
| No-double-mint | unique `id` per lock (vault-enforced) + token-layer `id` uniqueness |
| No-theft | `h_rcpt` binds recipient predicate at lock time |
| No-value-inflation | amount bound in receipt = genesis value; splits conserve |
| No-rogue-contract | `h_cfg` pins vault/asset; type's `VerifyIssuance` pins `h_cfg` |
| No-reorged-lock | trivial: per-block UC finality, no reorgs |
| Solvency | vault escrow ≥ outstanding minted supply (lock before mint) |
| No-double-release | nullifier mapping keyed by certified burn tx id |

Vault upgrades are timelocked and must preserve `h_cfg` (a config change is a **new
bridge deployment** with a new token type, per `app:bridging-upgrades`).

### 8.6 Disposition of tags 39042 / 39043

Supply policy is **bridge-only**: token-layer UCT exists solely via 39049 mints.
Tags 39042 (genesis allocation) and 39043 (validator reward) get **specified bodies**
(Appendix C.3: 39042 references the EVM genesis-allocation entry; 39043 carries
`(epoch, validatorId, amount, UC+MPT proof of the RewardsDistributor payout event)`)
but remain **unregistered in Γ on mainnet** (fail-shut): they are reserved provenance
labels for a possible future direct-mint path, and registering them would create a
second issuance root competing with the vault's solvency invariant.

---

## 9. Component Change List

### 9.1 `bft-core` / `bft-go-base`

- Relax `NodeInfo.IsValid()`: replace `Stake != 1 → error` with `Stake < 1 → error`
  (`root_trust_base.go:149`), gated on a consensus/config version so PoA networks are
  unaffected.
- REST intake (`PUT /api/v1/trustbases`) and `TrustBaseStore` chaining validation:
  **unchanged**.
- Optional (phase 2+): stake-weighted leader selection in
  `leader/reputation.go pickLeader()` / `sharding.go selectLeader()` — weighted
  choice by stake. Uniform selection remains *safe* meanwhile (quorum is already
  stake-weighted); this is an incentive/liveness optimization.
- Per-partition quorum rules: untouched this phase.
- **New:** `governance-agent` service (§5.1) in the `bft-core` repo.

### 9.2 `uni-evm`

- **P0:** harden precompile `0x…0100` signature verification (§6.3.1).
- Precompile v2 ABI + new `0x…0101` (§6.3.2–3).
- `BlockProducer`: coinbase → `FeeCollector` predeploy address; system-tx injection
  (§6.1); guest-program validity rule for the system tx.
- `genesis.json`: predeploys (all §4 contracts + proxies + `ProxyAdmin`), allocation
  buckets (§7.2), dev accounts removed for mainnet.
- `TrustBaseUpdater`: optional self-sourcing from `EpochManager` state (§6.3.4).
- Forced-inclusion inbox (§10, stage 1).

### 9.3 `state-transition-sdk-js`

- New `NativeBridgeMintJustification` (tag 39049) + verifier registered in
  `MintJustificationVerifierService`; EVM header/receipt-proof verification helpers;
  the native-bridged UCT token type definition; burn-reason format for bridge-out.

### 9.4 Yellowpaper

- Rewrite and **re-enable `governance.tex`**: the abstract Governance Body is
  instantiated as the EVM contract suite; the Validator Assignment Record flow is
  realized for the BFT Core set (this design becomes the normative content).
- `bft.tex`: trust-base stake sentence ("initially fixed to 1 …") becomes normative:
  stakes = epoch's locked amounts from the staking contracts.
- `appendix-token-types.tex`: register 39049 as specified; specify 39042/39043 bodies
  (reserved/unregistered).
- `appendix-bridging.tex`: new "Native Partition Bridging" section (§8, incl. the
  header↔IR binding).

### 9.5 Extension path (recorded, not built now)

Partition/shard validator assignment: a second `EpochManager` output per partition
feeding `PUT /api/v1/configurations` (`PartitionDescriptionRecord` already has
`Epoch`/`EpochStart`/`Validators`), realizing the governance chapter's Validator
Assignment Records — same agents, same chaining pattern.

---

## 10. EVM Partition Availability Roadmap

zk validity proofs give **safety** (no invalid state can certify); the roadmap is
about **liveness and censorship resistance**. Stage 1 is **launch-blocking** for DPoS:
a censoring sequencer could otherwise control validator-set changes.

1. **Hot standby sequencer + forced-inclusion inbox.** A user may submit a
   transaction (typically a staking or evidence tx) to BFT Core root nodes via a new
   inbox endpoint; the root chain commits an ordered digest of pending forced txs
   into the data it certifies (technical record / certification response). The
   **zk guest program enforces** that forced txs are included within `K` blocks —
   a block violating this is unprovable. No honest-sequencer assumption; the epoch
   extension rule (§5.4) backstops full stalls. A standby sequencer (shared key
   custody or key handover procedure) covers crash faults.
2. **Permissioned sequencer set** with round-robin leader rotation, the schedule
   certified by the root chain via the partition's shard configuration.
3. **Self-referential DPoS for the sequencer set**: sequencer selection by the same
   staking contracts (a second `EpochManager` output through
   `PUT /api/v1/configurations`) — this is also §9.5's partition-validator path.
4. **Full DA/witness publication** (blocks + execution witnesses posted to a
   BFT-certified DA channel) so any party can reconstruct state and take over
   sequencing permissionlessly.

---

## 11. Security Analysis

1. **Circularity (EVM ⇄ root chain).** Bootstrap: PoA genesis trust base. Induction:
   `TB(e+1)` is derived from state certified under `TB(e)` *and* signed by ≥ 2/3 of
   epoch-`e` stake — the standard chained weak-subjectivity argument. A corrupted
   epoch (> 1/3 stake malicious) can corrupt all future epochs; this is the same
   assumption every chained-PoS system makes and is stated honestly rather than
   hidden. The MPT cross-check in agents removes any additional trust in the EVM
   node software of any single party.
2. **Sequencer censorship of staking txs.** Mitigated by the forced-inclusion inbox
   with validity-proof-enforced inclusion (§10.1). Residual risk before stage 1
   ships is why stage 1 is launch-blocking. Epoch extension bounds the damage of a
   stalled (as opposed to censoring) sequencer: the incumbent set persists, no wrong
   set can activate.
3. **Long-range attacks.** Trust base records are hash+signature chained; clients
   (and the SDK) must reject trust-base forks branching earlier than the unbonding
   period (weak subjectivity window) and should pin recent trust-base hashes
   out-of-band (already the pattern in `app:bridging-settlement`'s allow-list).
4. **Unbonding vs windows (hard constraint).**
   `unbonding > evidenceWindow + downtimeWindow + maxEpochExtension`, so any stake
   that misbehaved while active is still bonded — and slashable — when evidence can
   land. Parameter bounds in Appendix D encode this as an invariant
   (`UnicityGovernance` rejects violating combinations).
5. **Slashing evidence availability.** Permissionless `submitSeal`/evidence paths +
   forced inclusion mean evidence delivery requires no cooperation from sequencer or
   accused validator; the submitter bounty (§4.6) makes enforcement incentive-
   compatible.
6. **Stake grinding / leader predictability.** The stake snapshot at `S_e` is fixed
   before any leader schedule derived from it; the schedule is deterministic.
   Predictable leaders are acceptable for HotStuff-style protocols (safety never
   depends on leader honesty) but enable targeted DoS — mitigate operationally
   (sentry nodes, multiaddr privacy); VRF-based rotation is future work.
7. **Governance capture.** `maxValidators` and optional per-validator stake caps;
   commission bounds; 7-day timelock on parameter changes; Foundation veto during
   the bootstrap phase (sunset governed by roadmap). Delegation concentration is
   visible on-chain; reputation tooling is future work.
8. **Precompile stub (P0).** The current `0x…0100` accepts unverified seals. Nothing
   in this design — SealRegistry, slashing, bridge-out — is deployable before the
   hardening of §6.3.1 lands and is audited.
9. **Bridge-out gas DoS.** The on-chain `VerifyToken` walk is attacker-pays and
   bounded by `maxHistoryLen`; oversized histories must compress on the token layer
   first (§8.4.3). Gas-cost model to be published with the vault implementation.
10. **zk prover failure.** Blocks stop certifying → the chain halts *safely* → epoch
    extension keeps consensus running on the incumbent set; LightClient witness mode
    is the degraded-path prover. Prover diversity is future work.
11. **Key management.** Three roles: owner key (EVM account, controls funds),
    consensus key (secp256k1, signs BFT votes), node id (derived from consensus
    key). `updateSigner` rotates the consensus key with next-epoch activation; a
    compromised consensus key can be rotated without fund movement, and slashing
    targets stake, not keys.
12. **Signature scheme roadmap.** The yellowpaper targets BLS-style accountable
    subgroup multisignatures; this design is agnostic — the signer bitmap abstraction
    in §6.3 survives the transition (the precompile then verifies an aggregate +
    bitmap instead of a signature map).

---

## 12. Deployment and Migration Plan

| Phase | Content | Rollback |
|---|---|---|
| **0** | Precompile hardening (§6.3.1) + `FeeCollector`/coinbase repoint. Independent of DPoS; ship early. | revert coinbase to 0x0 |
| **1** | Contract suite on testnet in **shadow mode**: `EpochManager` emits candidates, agents build + sign TBs, but the PoA set stays authoritative; outputs compared continuously. | disable agents |
| **2** | Testnet authoritative: `Stake ≥ 1` gate enabled, DPoS-produced TBs drive epochs; forced-inclusion inbox live (launch-blocking gate). | stop submitting TBs → epoch extension freezes incumbent set; re-pin PoA TB |
| **3** | Mainnet genesis: allocations (§7.2), predeploys, Foundation-weighted initial stake, `maxValidators` 25, gradual raise. | Foundation veto + epoch extension |
| **4** | Bridge activation: 39049 verifier registered in Γ, `NativeVault` unpaused. | pause vault (mint side fail-shut by deregistering 39049) |

---

## Appendix A — `TrustBaseCandidate` ↔ `RootTrustBaseV1` mapping

| RootTrustBaseV1 field | Source |
|---|---|
| `Version` | constant 1 |
| `NetworkID` | partition config (α) |
| `Epoch` | candidate `epoch` |
| `EpochStart` | candidate `epochStartRound` (`A_e`) |
| `RootNodes[i].NodeID` | candidate `entries[i].nodeId` |
| `RootNodes[i].SigKey` | candidate `entries[i].consensusPubKey` |
| `RootNodes[i].Stake` | candidate `entries[i].stake` (unit: whole UCT; u64) |
| `QuorumThreshold` | candidate `quorum` |
| `PreviousEntryHash` | `H(TB_e)` (agent-computed; candidate `prevHash` cross-check) |
| `Signatures` | collected from epoch-`e` agents (≥ 2/3 stake) |

Entries sorted by `nodeId` (bytewise); canonical CBOR per the yellowpaper's encoding
appendix; `keccak256(canonicalCbor(candidate))` is what `finalizeEpoch()` writes to
`TRUST_BASE_CANDIDATE_SLOT`. Stake denominated in whole UCT (floor), keeping u64
range.

## Appendix B — Double-sign evidence format

Evidence = `(payload₁, sig₁, payload₂, sig₂, pubkey)` where each payload is a
canonical BFT vote signing payload (the `SigBytes()` encoding of the seal /
`LedgerCommitInfo` as produced by `safety_module.go`). Precompile `0x…0101` parses
`(round, votedHash)` from each payload, verifies both signatures under `pubkey`, and
`SlashingManager` slashes iff `round₁ = round₂ ∧ votedHash₁ ≠ votedHash₂` and
`pubkey` maps to a validator bonded at that round (epoch lookup via `SealRegistry`).
The exact payload byte layout is normatively pinned to `bft-go-base`'s `SigBytes()`
and must be frozen in the yellowpaper as part of §9.4.

## Appendix C — CBOR bodies (sketch; normative versions go to the yellowpaper)

**C.1 39049 NativeBridgeMintReason** — `39049([uc, header, receiptProof, lockRecord])`
as in §8.1. Normative link: the verifier MUST check
`certifiedBinding(IR, header)` — the EVM partition's consistency-proof rule binding
the certified input record hash to the block (header hash ↔ `IR.h`); this rule is
defined by the partition type descriptor `SD` and must be frozen in the yellowpaper's
EVM-partition section.

**C.2 Bridge-out burn reason** — `(BURN_NATIVE_DOMAIN, h_cfg, evmRecipient(20B),
amount, salt)`; burn tx id = `H(BURN_DOMAIN, sid_b, txhash_b)` (as
`app:bridging-nullifier`).

**C.3 39042 / 39043 (specified, unregistered)** —
`39042([h_genesisConfig, bucketId, allocationEntry])`;
`39043([epoch, validatorId, amount, uc, payoutEventProof])`. Reserved provenance
labels; not in Γ on mainnet (§8.6).

## Appendix D — Parameter table (defaults / bounds)

| Parameter | Default | Bounds | Notes |
|---|---|---|---|
| `epochLength` | ~1 day of rounds | 1 h – 7 d | |
| `Δ` (activation margin) | ~1.5 h | 30 min – 12 h | |
| `maxValidators` | 25 | 4 – 500 | raise gradually |
| `minSelfStake` | 100,000 | ≥ 1,000 | |
| `minDelegation` | 100 | ≥ 1 | |
| `unbondingPeriod` | 21 d | > windows sum (§11.4) | invariant-checked |
| `slashFractionDoubleSign` | 5% | 1–100% | |
| `slashFractionDowntime` | 0.1% | 0.01–5% | |
| `downtimeWindow W` / `d_min` | 10,000 rounds / 0.5 | | |
| `p_min` (reward floor) | 0.9 | 0.5–1.0 | |
| `commissionChangeLimit` | 1 pp/epoch | | |
| `burnBps` (fee split) | 50% | 0–100% | |
| `E_0`, `r` (emission) | 10% APR @ 30% staked, 0.85 | pool-capped | |
| `maxHistoryLen` (bridge-out) | impl-defined | gas-model-bound | |
| `timelock` | 7 d | ≥ 2 d | |

## Appendix E — Polygon reuse/rewrite matrix (to complete during implementation)

| Polygon file | Action | Notes |
|---|---|---|
| `StakeManager.sol` | fork, heavy edit | drop checkpoint/ERC20/heimdall paths; native staking |
| `ValidatorShare.sol` | fork, light edit | native transfers; reward inflow via RewardsDistributor |
| `StakingInfo.sol` | replace | events kept where useful |
| `SlashingManager.sol` | replace mostly | on-chain evidence instead of heimdall consensus |
| `Governance.sol` / `Registry.sol` | fork, light edit | timelock added |
| checkpoint / StateSender / RootChain | **not ported** | obsolete in this topology |
| License audit | **pre-fork checklist** | mixed MIT/GPL headers in upstream repo |
