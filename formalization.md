# Formalization overview

Lean 4 formalization of [*Beluga: Block Synchronization for BFT Consensus
Protocols*](docs/Block_Sync_Project.pdf).

## Paper → code map

The single source of truth for which paper item lives where in this repo.
Status: ✅ done · ◐ in progress · ☐ planned · ⊘ out of scope · ⏸ deferred.

### §2 — Network model and synchronizer abstraction

| Paper | Code | Status |
|---|---|---|
| §2 — Network model (`n`, `f`, `k`, `GST`, `Δ`) | [`System.lean :: BlockSynchroniserSystem`](BlockSynchroniser/System.lean) | ✅ |
| §2 — Honest / Byzantine partition | [`System.lean :: isHonest` / `isByzantine`](BlockSynchroniser/System.lean) | ◐ binary; crashed-validator refinement deferred |
| §2.1 — Block structure (`r, d, author, parents, payload, signature`) | [`Block.lean :: Block`](BlockSynchroniser/Block.lean) | ◐ signature omitted (irrelevant to abstract synchronizer) |
| §2.1 — Synchronizer interface (`block_propose_i`/`block_accept_i`/`block_store_i`) | [`Operations.lean :: ValidatorOperation`](BlockSynchroniser/Operations.lean) | ✅ |
| §2.1 — Causal history `causal(B)` | [`Causal.lean :: Reaches` / `causal`](BlockSynchroniser/Causal.lean) | ✅ |
| §2.1 — **Definition 1.1 — Round-Progression** | [`Properties.lean :: RoundProgression`](BlockSynchroniser/Properties.lean) | ✅ |
| §2.1 — **Definition 1.2 — Round-Termination** | [`Properties.lean :: RoundTermination`](BlockSynchroniser/Properties.lean) | ✅ |
| §2.1 — **Definition 1.3 — Block availability** | [`Properties.lean :: BlockAvailability`](BlockSynchroniser/Properties.lean) | ✅ |
| §2.1 — **Definition 1.4 — Causal availability** | [`Properties.lean :: CausalAvailability`](BlockSynchroniser/Properties.lean) | ✅ |
| §2.1 — **Definition 1** (block synchronizer = conjunction) | [`Properties.lean :: BlockSynchronizer`](BlockSynchroniser/Properties.lean) | ✅ |

### §4 — The Beluga protocol

| Paper | Code | Status |
|---|---|---|
| §4.1 — Block extensions (`weaklinks`, `watermark`, `ancestors`) | [`Beluga/BlockExt.lean :: BelugaBlock`](BlockSynchroniser/Beluga/BlockExt.lean) | ✅ |
| §4.2 — Reputation mechanism | `Beluga/Reputation.lean` | ☐ Phase 4 |
| §4.2 — Admission Control + parent selection | `Beluga/AdmissionControl.lean` | ☐ Phase 4 |
| §4.3 — ImPoA (implicit proof-of-availability) + live/bulk classification | `Beluga/Pull.lean` | ☐ Phase 4 |
| §4.3 — Random pull complexity bound (`O(1)`) | — | ⊘ probabilistic |
| §4.4 — Availability pattern | [`Beluga/Patterns.lean :: availabilityPattern`](BlockSynchroniser/Beluga/Patterns.lean) | ✅ strong-link only |
| §4.4 — Certificate pattern | [`Beluga/Patterns.lean :: certificatePattern`](BlockSynchroniser/Beluga/Patterns.lean) | ✅ |
| §4.4 — `available` / `certified` | [`Beluga/Patterns.lean`](BlockSynchroniser/Beluga/Patterns.lean) | ✅ |
| §4.4 — Uniqueness consequence ("for any validator and round, at most one block can become certified") | [`Beluga/Patterns.lean :: certified_unique`](BlockSynchroniser/Beluga/Patterns.lean) | ◐ stated; `sorry` (queued for Aristotle round 2) |

### §5 — Beluga's main theorems (Phase 5)

| Paper | Code | Status |
|---|---|---|
| §5 — **Lemma 1** — after GST, all honest validators reach the same round within 3Δ | `Beluga/Theorems.lean :: lemma1_honest_round_entry` | ☐ |
| §5 — **Lemma 2** — round-to-round latency ≤ 3Δ in the happy case | `Beluga/Theorems.lean :: lemma2_round_latency` | ☐ |
| §5 — **Theorem 1** — Beluga ⊨ Block availability | `Beluga/Theorems.lean :: theorem1_block_availability` | ☐ |
| §5 — **Theorem 2** — Beluga ⊨ Causal availability | `Beluga/Theorems.lean :: theorem2_causal_availability` | ☐ |
| §5 — **Theorem 3** — Beluga ⊨ Round-Progression | `Beluga/Theorems.lean :: theorem3_round_progression` | ☐ |
| §5 — **Theorem 4** — Beluga ⊨ Round-Termination | `Beluga/Theorems.lean :: theorem4_round_termination` | ☐ |

### Appendix C — Performance bounds

| Paper | Status |
|---|---|
| **Lemmas 3, 4, 5** — deterministic worst-case latency bounds | ⊘ Out of scope (performance, not safety/liveness) |
| **Lemmas 6, 7** + **Theorem 5** — expected-latency bounds | ⊘ Probabilistic; out of scope |

### Appendix D — Mysticeti-Beluga (Phase 6)

| Paper | Code | Status |
|---|---|---|
| D.1.1 — Direct / indirect decision rules | `Mysticeti/Consensus.lean :: decisionRule` | ☐ |
| D.1.2 — Round-robin leader schedule | `Mysticeti/Consensus.lean :: leaderSchedule` | ☐ |
| **Lemma 8** — leader block referenced next round (after GST) | `Mysticeti/Liveness.lean :: lemma8_leader_referenced` | ⏸ liveness side; deferred |
| **Lemma 9** — honest validators create certificate for honest leader | `Mysticeti/Liveness.lean :: lemma9_honest_certificate` | ⏸ liveness side |
| **Lemma 10** — round-robin pigeonhole (3 consecutive honest leaders in any 3f+3 window) | `Mysticeti/Safety.lean :: lemma10_round_robin_pigeonhole` | ☐ pure combinatorics |
| **Lemma 11** — undecided leader block eventually decided | `Mysticeti/Liveness.lean :: lemma11_eventual_decision` | ⏸ liveness side |
| **Lemma 12** — block referenced by 2f+1 ⇒ honest validators output `block_accept` | `Mysticeti/Liveness.lean :: lemma12_referenced_accepted` | ⏸ liveness side |
| **Lemma 13** — certificate persistence across rounds | `Mysticeti/Safety.lean :: lemma13_cert_persistence` | ☐ |
| **Lemma 14** — no honest validator skips a directly-committed leader | `Mysticeti/Safety.lean :: lemma14_no_skip` | ☐ |
| **Lemma 15** — at most one certified leader per round | `Mysticeti/Safety.lean :: lemma15_unique_cert` | ☐ specialization of `Beluga/Patterns.lean :: certified_unique` |
| **Lemma 16** — consistent leader-status decision across honest validators | `Mysticeti/Safety.lean :: lemma16_consistent_status` | ☐ |
| **Theorem 6** — Mysticeti-Beluga consensus liveness | `Mysticeti/Liveness.lean :: theorem6_consensus_liveness` | ⏸ deferred |
| **Theorem 7** — Mysticeti-Beluga consensus safety | `Mysticeti/Safety.lean :: theorem7_consensus_safety` | ☐ |

## Not in the paper — internal validation

The `golden_*`, `realizable_*`, and `not_*_emptyTrace` lemmas in
[`Validation.lean`](BlockSynchroniser/Validation.lean) **are not paper
results.** They are sanity checks demonstrating that our Lean version of
each Definition-1 property is satisfiable / falsifiable by concrete traces
(non-vacuity validation). The opening comment of `Validation.lean` spells
out the distinction.

## Where to look

| | |
|---|---|
| Detailed item-by-item status | [docs/formalization-status.md](docs/formalization-status.md) |
| Phased plan & scope decisions | [docs/formalization-plan.md](docs/formalization-plan.md) |
| Aristotle delegation workflow | [docs/aristotle-workflow.md](docs/aristotle-workflow.md) |
| Aristotle project tracker (active / queued / completed submissions) | [docs/aristotle-projects.md](docs/aristotle-projects.md) |
| Per-stage changelog | [changelogs/](changelogs/) |
| The paper | [docs/Block_Sync_Project.pdf](docs/Block_Sync_Project.pdf) |

## Repository layout

```
block-sync-lean/
├── formalization.md            ← you are here
├── README.md                   ← build / run instructions
├── docs/                       ← plan, status, workflow, paper
├── changelogs/                 ← timestamped per-stage entries
├── BlockSynchroniser/
│   ├── Block, Validator, Operations.lean
│   ├── System, State, Trace.lean
│   ├── Causal.lean             ← inductive Reaches / causal
│   ├── Quorum.lean             ← BFT quorum-intersection
│   ├── Properties.lean         ← Definition 1.1–1.4
│   ├── Validation.lean         ← non-vacuity sanity checks
│   └── Beluga/
│       ├── BlockExt.lean       ← BelugaBlock (§4.1)
│       ├── Patterns.lean       ← available/certified (§4.4)
│       ├── Reputation.lean     ← Phase 4
│       ├── AdmissionControl.lean ← Phase 4
│       ├── Pull.lean           ← Phase 4 (ImPoA)
│       ├── Protocol.lean       ← Phase 4 (HonestStep + executable step)
│       └── Theorems.lean       ← Phase 5 (Lemmas 1–2, Theorems 1–4)
├── Main.lean
├── lakefile.lean
└── lean-toolchain              ← v4.28.0
```

Mysticeti-Beluga modules (Phase 6, optional) live under
`BlockSynchroniser/Mysticeti/`.

## Build

```bash
lake update
lake build
```

Toolchain pinned to `leanprover/lean4:v4.28.0` — matches Aristotle's pinned
version exactly, so submissions compile cleanly on both sides.
