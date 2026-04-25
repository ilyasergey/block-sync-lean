# Formalization overview

Lean 4 formalization of [*Beluga: Block Synchronization for BFT Consensus
Protocols*](docs/Block_Sync_Project.pdf).

> **Mechanization findings:** see
> [`docs/mechanization-findings.md`](docs/mechanization-findings.md)
> for a paper-side log of observations the formalization surfaced
> (paper terminology, no Lean — written so it can be folded back into
> the paper). Headline finding so far: **F-1, scheduler-fairness
> assumption missing from Lemmas 1 & 2** — see also
> [`docs/paper-feedback-l1-l2-fairness.md`](docs/paper-feedback-l1-l2-fairness.md).

## Paper → code map

The single source of truth for which paper item lives where in this repo.
Status: ✅ done · ◐ in progress · ☐ planned · ⊘ out of scope · ⏸ deferred.

### §2 — Network model and synchronizer abstraction

| Paper | Code | Status |
|---|---|---|
| §2 — Network model (`n`, `f`, `k`, `GST`, `Δ`) | [`System.lean :: BlockSynchroniserSystem`](BlockSynchroniser/System.lean) | ✅ |
| §2 — Honest / Byzantine partition | [`System.lean :: isHonest` / `isByzantine`](BlockSynchroniser/System.lean) | ✅ |
| §2.1 — Block structure (`r, d, author, parents, payload, signature`) | [`Block.lean :: Block`](BlockSynchroniser/Block.lean) | ✅ (signature field omitted — see note below) |
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
| §4.2 — Reputation mechanism (increase / decrease rules; Figure 8 lines 23–32) | [`Beluga/Reputation.lean`](BlockSynchroniser/Beluga/Reputation.lean) (`reputationIncreaseCandidates`, `updateScoreWithWatermarks`, `reputationPenalty`, `reputationThreshold`, `aboveThreshold`) | ✅ |
| §4.2 — Admission Control + parent selection (Figure 8 lines 14–17 + round-advancement rule (i)) | [`Beluga/AdmissionControl.lean`](BlockSynchroniser/Beluga/AdmissionControl.lean) (`acParentSelection`, `canAdvanceByQuorum`) | ✅ |
| §4.3 — ImPoA (implicit proof-of-availability) + live/bulk classification | [`Beluga/Pull.lean`](BlockSynchroniser/Beluga/Pull.lean) (`implicitlyAvailable`, `isLive`, `classifyMissing`, `isAcceptableImPoA`) | ✅ strong-link only; weak-link inclusion deferred |
| §4 — `BelugaState`, `BelugaValidator`, `ReputationTable` | [`Beluga/State.lean`](BlockSynchroniser/Beluga/State.lean) | ✅ |
| §4 — Protocol semantics: `HonestStep` (relational) + executable `step` + `belugaTrace` | [`Beluga/Protocol.lean`](BlockSynchroniser/Beluga/Protocol.lean) | ◐ Definitions ✅; the refinement lemma `step_refines_HonestStep` (with paper-consistent `HonestAccept`/`HonestStore` preconditions + `BelugaState.WellFormed`) is currently `sorry` |
| §4 — Executable demos (`#eval`, `lake exe blocksynchroniser`) | [`Beluga/Examples.lean`](BlockSynchroniser/Beluga/Examples.lean) (`system4`, `run`, `reprLog`, `proposersFor`) | ✅ |
| §4.3 — Random pull complexity bound (`O(1)`) | — | ⊘ probabilistic |
| §4.4 — Availability pattern | [`Beluga/Patterns.lean :: availabilityPattern`](BlockSynchroniser/Beluga/Patterns.lean) | ✅ strong-link only |
| §4.4 — Certificate pattern | [`Beluga/Patterns.lean :: certificatePattern`](BlockSynchroniser/Beluga/Patterns.lean) | ✅ |
| §4.4 — `available` / `certified` | [`Beluga/Patterns.lean`](BlockSynchroniser/Beluga/Patterns.lean) | ✅ |
| §4.4 — Uniqueness consequence ("for any validator and round, at most one block can become certified") | [`Beluga/Patterns.lean :: certified_unique`](BlockSynchroniser/Beluga/Patterns.lean) | ◐ stated; `sorry` |

### §5 — Beluga's main theorems (Phase 5)

| Paper | Code | Status |
|---|---|---|
| §5 — **Lemma 1** — after GST, all honest validators reach the same round within 3Δ | [`Beluga/Theorems.lean :: lemma1_honest_round_entry`](BlockSynchroniser/Beluga/Theorems.lean) | ◐ Stated with timing (`time k ≥ GST + 3Δ`); `sorry` + paper sketch |
| §5 — **Lemma 2** — round-to-round latency ≤ 3Δ in the happy case | [`Beluga/Theorems.lean :: lemma2_round_latency`](BlockSynchroniser/Beluga/Theorems.lean) | ◐ Stated with timing (`time k' ≤ time k + 3Δ`); `sorry` + paper sketch |
| §5 — **Theorem 1** — Beluga ⊨ Block availability | [`Beluga/Theorems.lean :: theorem1_block_availability`](BlockSynchroniser/Beluga/Theorems.lean) | ◐ Stated; `sorry` + paper sketch |
| §5 — **Theorem 2** — Beluga ⊨ Causal availability | [`Beluga/Theorems.lean :: theorem2_causal_availability`](BlockSynchroniser/Beluga/Theorems.lean) | ◐ Stated; `sorry` + paper sketch |
| §5 — **Theorem 3** — Beluga ⊨ Round-Progression | [`Beluga/Theorems.lean :: theorem3_round_progression`](BlockSynchroniser/Beluga/Theorems.lean) | ◐ Stated; `sorry` + paper sketch |
| §5 — **Theorem 4** — Beluga ⊨ Round-Termination | [`Beluga/Theorems.lean :: theorem4_round_termination`](BlockSynchroniser/Beluga/Theorems.lean) | ◐ Stated; `sorry` + paper sketch |
| §5 corollary — Beluga is a block synchronizer (T1∧T2∧T3∧T4) | [`Beluga/Theorems.lean :: belugaTrace_isBlockSynchronizer`](BlockSynchroniser/Beluga/Theorems.lean) | ◐ Conjunction proved trivially as `⟨T3, T4, T1, T2⟩`, but T1–T4 are themselves `sorry`, so the corollary is not fully proven yet |

### Appendix C — Performance bounds

| Paper | Code | Status |
|---|---|---|
| **Assumption 1 — latency triangle** (honest-to-honest direct delivery is faster than any relay through an intermediate validator) | [`Beluga/PerformanceLemmas.lean :: LatencyTriangle`](BlockSynchroniser/Beluga/PerformanceLemmas.lean) | ✅ Definition. Adapted to the trace model: post-GST, if all honest validators are at round `r` they all reach `r+1` within `Δ`. Used as a hypothesis to **L4** and **L5** below. |
| **Lemma 3** — honest validators are not blamed (post-GST) | [`Beluga/PerformanceLemmas.lean :: lemma3_honest_not_blamed`](BlockSynchroniser/Beluga/PerformanceLemmas.lean) | ◐ Body proven; transitively depends on `Beluga/StepPreservation.lean :: tryActFor_preserves_reputation` which is currently `sorry` |
| **Lemma 4** — round latency Δ when honest reputations dominate | [`Beluga/PerformanceLemmas.lean :: lemma4_round_latency_delta`](BlockSynchroniser/Beluga/PerformanceLemmas.lean) | ✅ Takes `LatencyTriangle` (Assumption 1, see above) as an explicit hypothesis |
| **Lemma 5** — round latency 2Δ-or-blame (deterministic part) | [`Beluga/PerformanceLemmas.lean :: lemma5_round_latency_or_blamed`](BlockSynchroniser/Beluga/PerformanceLemmas.lean) | ✅ Same `LatencyTriangle` hypothesis as L4 |
| **Lemmas 6, 7** + **Theorem 5** — expected-latency bounds | — | ⊘ Probabilistic; genuinely out of scope (would need a probability framework) |

### Appendix D — Mysticeti-Beluga (Phase 6)

| Paper | Code | Status |
|---|---|---|
| D.1.1 — Direct / indirect decision rules | [`Mysticeti/Consensus.lean :: directDecide` / `indirectDecideStep`](BlockSynchroniser/Mysticeti/Consensus.lean) | ✅ |
| D.1.1 — Skip pattern / certificate pattern (at next round) | [`Mysticeti/Consensus.lean :: skipPattern` / `certificatePatternAt`](BlockSynchroniser/Mysticeti/Consensus.lean) | ✅ |
| D.1.2 — Round-robin leader schedule | [`Mysticeti/Consensus.lean :: leaderOf` / `isLeaderBlock`](BlockSynchroniser/Mysticeti/Consensus.lean) | ✅ |
| **Lemma 8** — leader block referenced next round (after GST) | [`Mysticeti/Liveness.lean :: lemma8_leader_referenced`](BlockSynchroniser/Mysticeti/Liveness.lean) | ◐ Stated with timing (post-GST + 4Δ bound); `sorry` + paper sketch |
| **Lemma 9** — honest validators create certificate for honest leader | [`Mysticeti/Liveness.lean :: lemma9_honest_certificate`](BlockSynchroniser/Mysticeti/Liveness.lean) | ◐ Stated; `sorry` + paper sketch |
| **Lemma 10** — round-robin pigeonhole (3 consecutive honest leaders in any 3f+3 window) | [`Mysticeti/Safety.lean :: lemma10_round_robin_pigeonhole`](BlockSynchroniser/Mysticeti/Safety.lean) | ◐ Stated; `sorry` + paper sketch (pure combinatorics) |
| **Lemma 11** — undecided leader block eventually decided | [`Mysticeti/Liveness.lean :: lemma11_eventual_decision`](BlockSynchroniser/Mysticeti/Liveness.lean) | ◐ Stated with timing; `sorry` + paper sketch |
| **Lemma 12** — block referenced by 2f+1 ⇒ honest validators output `block_accept` | [`Mysticeti/Liveness.lean :: lemma12_referenced_accepted`](BlockSynchroniser/Mysticeti/Liveness.lean) | ◐ Stated with timing; `sorry` + paper sketch |
| **Lemma 13** — certificate persistence across rounds | [`Mysticeti/Safety.lean :: lemma13_cert_persistence`](BlockSynchroniser/Mysticeti/Safety.lean) | ◐ Stated (skeleton conclusion); `sorry` + paper sketch |
| **Lemma 14** — no honest validator skips a directly-committed leader | [`Mysticeti/Safety.lean :: lemma14_no_skip`](BlockSynchroniser/Mysticeti/Safety.lean) | ◐ Stated (skeleton); `sorry` + paper sketch |
| **Lemma 15** — at most one certified leader per round | [`Mysticeti/Safety.lean :: lemma15_unique_cert`](BlockSynchroniser/Mysticeti/Safety.lean) | ◐ Reduces to `Beluga/Patterns.lean :: certified_unique` (which is itself sorry'd) |
| **Lemma 16** — consistent leader-status decision across honest validators | [`Mysticeti/Safety.lean :: lemma16_consistent_status`](BlockSynchroniser/Mysticeti/Safety.lean) | ◐ Skeleton; `sorry` + paper sketch |
| **Theorem 6** — Mysticeti-Beluga consensus liveness | [`Mysticeti/Liveness.lean :: theorem6_consensus_liveness`](BlockSynchroniser/Mysticeti/Liveness.lean) | ◐ Skeleton statement; `sorry` + paper sketch |
| **Theorem 7** — Mysticeti-Beluga consensus safety | [`Mysticeti/Safety.lean :: theorem7_consensus_safety`](BlockSynchroniser/Mysticeti/Safety.lean) | ◐ Skeleton; `sorry` + paper sketch |

## Not in the paper — internal validation

The `golden_*`, `realizable_*`, and `not_*_emptyTrace` lemmas in
[`Validation.lean`](BlockSynchroniser/Validation.lean) **are not paper
results.** They are sanity checks demonstrating that our Lean version of
each Definition-1 property is satisfiable / falsifiable by concrete traces
(non-vacuity validation). The opening comment of `Validation.lean` spells
out the distinction.

All four `golden_*` theorems are proved sorry-free; the realizability
and anti-witness lemmas are also closed. Per-proof provenance (which
proofs were filled by Aristotle vs hand) lives in
[docs/aristotle-attributions.md](docs/aristotle-attributions.md).

## Notes on paper consistency

Side conditions and refinements added during formalization that aren't
literally in the paper but are *consistent* with it (i.e., paper claims
hold under these). Reported here so a reader can spot them.

### Omitted paper structure (out of scope, no theorem affected)

- **`signature` field on `Block`** (paper §2.1). The paper's block
  carries six fields `(r, d, author, parents, payload, signature)`;
  our [`Block.lean :: Block`](BlockSynchroniser/Block.lean) carries
  the first five. Signature semantics are not invoked by any theorem
  in the scope we formalize — the abstract block synchronizer (and
  every paper theorem we target) treats Byzantine behavior
  adversarially via the honest/Byzantine partition rather than via
  signature-based attribution. Adding `signature` would only add
  data fields and a `verify` predicate that no proof references.

### Added side conditions (don't invalidate paper claims)

- **`n = 3 * f + 1`** (on `Quorum.quorumIntersection` and
  `Mysticeti/Safety.lean :: lemma10_round_robin_pigeonhole`).
  The paper writes `f < n/3` (equiv. `n ≥ 3f+1`) and uses `2f+1`-quorums
  consistently — which only gives a `≥ f+1` intersection bound when
  `n = 3f+1` exactly. For `n > 3f+1` the paper's quorum size implicitly
  scales (or the bound weakens). We pin the lemma to `n = 3f+1`, which
  matches the paper's worked examples and is unambiguous.
- **`(system.validators.filter (·.2 = true)).length = 2 * f + 1`** (on
  `lemma10_round_robin_pigeonhole`). Paper says "there are `2f+1`
  honest validators" — we surface this as an explicit hypothesis since
  our `system` allows `n ≥ 3f+1`; combined with `n = 3f+1` it's
  redundant, but stated explicitly for clarity.
- **`BelugaState.WellFormed system s`** (on
  `Beluga/Protocol.lean :: step_refines_HonestStep`): every entry in
  `s.validators` is registered in `system.validators`. Paper takes this
  as obvious (a state's validators are *the* system's validators); we
  add it explicitly because our `BelugaState` data type doesn't enforce
  it by construction.
- **`NoEquivocationInParents` (cross-block form)** in
  `Beluga/Patterns.lean`: extends paper's "honest validators don't
  equivocate" from within-one-block to *across* honest blocks (any two
  honest-authored blocks in the state agree on parents at the same
  `(author, round)`). Needed for the `certified_unique` proof in the
  case where the shared honest validator authored two distinct blocks
  each referencing one of the two certified candidates. The paper
  states this only in passing; we surface it.
- **`LatencyTriangle system time`** (on
  `Beluga/PerformanceLemmas.lean :: lemma4_round_latency_delta` and
  `lemma5_round_latency_or_blamed`). This is paper Assumption 1
  (latency triangle) adapted to our trace model: post-GST, if all
  honest validators are synchronized at round `r`, they all reach
  round `r+1` within `Δ`. The paper invokes Assumption 1 implicitly
  in the proofs of L4 and L5; we make it an explicit hypothesis so
  the dependency is transparent.

### Suspected ambiguity / minor inconsistency

- **Paper §4.2 increase rule vs. Figure 8 lines 24–29**. The prose says
  `B.watermark[j] = r-1` triggers the reputation increase; the
  pseudocode says `B'.watermark[j] == r-2`. Off-by-one due to timing
  framing (post- vs. pre-round-creation). Resolution: we follow the
  prose (`r-1`); both are consistent if the procedure is invoked at
  the right moment relative to round increment. Documented inline in
  `Beluga/Reputation.lean`.

- **Paper Lemma 5 (Appendix C)** mixes "expected latency" with "or at
  least one malicious validator is blamed" disjunction. The expected
  side is probabilistic; the disjunctive deterministic side is what we
  formalize as `lemma5_round_latency_or_blamed`. Not strictly an
  inconsistency — the paper combines two statements; we split them.

If anything in the formalization turns out to be a *real* inconsistency
with the paper (i.e., a paper claim cannot be proved as stated), it
will be flagged here and in [`docs/aristotle-attributions.md`](docs/aristotle-attributions.md)
under "Issues found while formalizing".

Currently no real inconsistencies detected — only the side conditions
above.

## Where to look

| | |
|---|---|
| Detailed item-by-item status | [docs/formalization-status.md](docs/formalization-status.md) |
| Phased plan & scope decisions | [docs/formalization-plan.md](docs/formalization-plan.md) |
| Aristotle delegation workflow | [docs/aristotle-workflow.md](docs/aristotle-workflow.md) |
| Aristotle project tracker (active / queued / completed submissions) | [docs/aristotle-projects.md](docs/aristotle-projects.md) |
| Aristotle attribution log (which proofs Aristotle filled, for the final report) | [docs/aristotle-attributions.md](docs/aristotle-attributions.md) |
| The "math tactical wall" — when to delegate vs hand-prove | [docs/math-tactical-wall.md](docs/math-tactical-wall.md) |
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
│   ├── Timing.lean             ← TimeMap, PartiallySynchronous
│   ├── Causal.lean             ← inductive Reaches / causal
│   ├── Quorum.lean             ← BFT quorum-intersection
│   ├── Properties.lean         ← Definition 1.1–1.4
│   ├── Validation.lean         ← non-vacuity sanity checks
│   ├── Beluga/
│   │   ├── BlockExt.lean       ← BelugaBlock (§4.1)
│   │   ├── Patterns.lean       ← available/certified (§4.4)
│   │   ├── State.lean          ← BelugaState + ReputationTable
│   │   ├── Reputation.lean     ← §4.2 update rules
│   │   ├── AdmissionControl.lean ← §4.2 parent selection
│   │   ├── Pull.lean           ← §4.3 ImPoA + live/bulk
│   │   ├── Protocol.lean       ← HonestStep + executable step
│   │   ├── Examples.lean       ← system4, run, #eval smoke tests
│   │   └── Theorems.lean       ← Lemmas 1–2, Theorems 1–4
│   └── Mysticeti/
│       ├── Consensus.lean      ← decision rules + leader schedule (D.1)
│       ├── Safety.lean         ← Lemmas 10, 13–16, Theorem 7 (D.3)
│       └── Liveness.lean       ← Lemmas 8, 9, 11, 12, Theorem 6 (D.2)
├── Main.lean                   ← drives the executable Beluga trace
├── lakefile.lean
└── lean-toolchain              ← v4.28.0
```

## Build

```bash
lake update
lake build
```

Toolchain pinned to `leanprover/lean4:v4.28.0` — matches Aristotle's pinned
version exactly, so submissions compile cleanly on both sides.

## Runnable examples

The executable Beluga `step` function (paper §4 protocol; round-robin honest
schedule) is fully implemented and `#eval`-able. Run it directly:

```bash
lake exe blocksynchroniser
```

This drives 20 executable `step` calls on a 4-validator, 1-Byzantine-budget
honest system (see [`BlockSynchroniser/Beluga/Examples.lean :: system4`](BlockSynchroniser/Beluga/Examples.lean))
and prints the resulting operation log. Sample output:

```
=== Beluga honest-synchronous trace ===
system: n=4, f=1, k=0, all 4 validators honest

After 20 executable `step` calls:
  total ops emitted: 20
  blocks in pool:    3
  round-0 distinct proposers: [0, 1, 2]

Operation log:
  0: propose vid=0 round=0 digest=0 parents=[]
  1: accept  vid=0 digest=0
  2: store   vid=0 digest=0
  3: propose vid=1 round=0 digest=1 parents=[]
  4: accept  vid=0 digest=1
  ...
```

`#eval` smoke tests in [`Examples.lean`](BlockSynchroniser/Beluga/Examples.lean)
exercise:

- `(run n).emittedOperations.length` — total ops after `n` steps.
- `proposersFor (run n) r` — distinct round-`r` proposers.
- `reprLog (run n)` — pretty-printed op log.

The schedule is round-robin: each step scans validators in id order and
applies the first available action (priority: propose → accept → store →
advance). vid 0 exhausts its actions before vid 1 takes over, then vid 2,
then vid 3.
