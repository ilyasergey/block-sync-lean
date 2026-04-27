# Formalization overview

Lean 4 formalization of [*Beluga: Block Synchronization for BFT Consensus
Protocols*](docs/Block_Sync_Project.pdf).

## Paper → code map

The single source of truth for which paper item lives where in this repo.
Status: ✅ done · ◐ in progress · ☐ planned · ⊘ out of scope · ⏸ deferred · ⚠️ proved but with paper-faithfulness concerns flagged in [`docs/mechanization-findings.md`](docs/mechanization-findings.md).

### §2 — Network model and synchronizer abstraction

| Paper | Code | Status |
|---|---|---|
| §2 — Network model (`n`, `f`, `k`, `GST`, `Δ`) | [`System.lean :: BlockSynchroniserSystem`](BlockSynchroniser/System.lean#L21) | ✅ |
| §2 — Honest / Byzantine partition | [`System.lean :: isHonest` / `isByzantine`](BlockSynchroniser/System.lean#L47) | ✅ |
| §2.1 — Block structure (`r, d, author, parents, payload, signature`) | [`Block.lean :: Block`](BlockSynchroniser/Block.lean#L22) | ✅ — signature field omitted (see note below); digest determinism (F-11) is carried as a side condition rather than baked into the field itself. |
| §2.1 — Synchronizer interface (`block_propose_i`/`block_accept_i`/`block_store_i`) | [`Operations.lean :: ValidatorOperation`](BlockSynchroniser/Operations.lean#L17) | ✅ |
| §2.1 — Causal history `causal(B)` | [`Causal.lean :: Reaches` / `causal`](BlockSynchroniser/Causal.lean#L27) | ✅ |
| §2.1 — **Definition 1.1 — Round-Progression** | [`Properties.lean :: RoundProgression`](BlockSynchroniser/Properties.lean#L27) | ✅ |
| §2.1 — **Definition 1.2 — Round-Termination** | [`Properties.lean :: RoundTermination`](BlockSynchroniser/Properties.lean#L46) | ✅ |
| §2.1 — **Definition 1.3 — Block availability** | [`Properties.lean :: BlockAvailability`](BlockSynchroniser/Properties.lean#L65) | ✅ |
| §2.1 — **Definition 1.4 — Causal availability** | [`Properties.lean :: CausalAvailability`](BlockSynchroniser/Properties.lean#L79) | ✅ |
| §2.1 — **Definition 1** (block synchronizer = conjunction) | [`Properties.lean :: BlockSynchronizer`](BlockSynchroniser/Properties.lean#L93) | ✅ |

### §4 — The Beluga protocol

| Paper | Code | Status |
|---|---|---|
| §4.1 — Block extensions (`weaklinks`, `watermark`, `ancestors`) | [`Beluga/BlockExt.lean :: BelugaBlock`](BlockSynchroniser/Beluga/BlockExt.lean#L31) | ✅ |
| §4.2 — Reputation mechanism (increase / decrease rules; Figure 8 lines 23–32) | [`Beluga/Reputation.lean`](BlockSynchroniser/Beluga/Reputation.lean#L23) | ✅ — we follow the prose `r-1` form (finding F-6 records the prose-vs-Figure-8 off-by-one). |
| §4.2 — Admission Control + parent selection (Figure 8 lines 14–17 + round-advancement rule (i)) | [`Beluga/AdmissionControl.lean`](BlockSynchroniser/Beluga/AdmissionControl.lean#L60) | ✅ |
| §4.3 — ImPoA (implicit proof-of-availability) + live/bulk classification | [`Beluga/Pull.lean`](BlockSynchroniser/Beluga/Pull.lean#L30) | ✅ — strong-link only; weak-link inclusion deferred. |
| §4 — `BelugaState`, `BelugaValidator`, `ReputationTable` | [`Beluga/State.lean`](BlockSynchroniser/Beluga/State.lean#L91) | ✅ |
| §4 — Protocol semantics: `HonestStep` (relational) + executable `step` + `belugaTrace` | [`Beluga/Protocol.lean`](BlockSynchroniser/Beluga/Protocol.lean#L192) | ✅ |
| §4 — Executable demos (`#eval`, `lake exe blocksynchroniser`) | [`Beluga/Examples.lean`](BlockSynchroniser/Beluga/Examples.lean#L17) | ✅ |
| §4.3 — Random pull complexity bound (`O(1)`) | — | ⊘ probabilistic |
| §4.4 — Availability pattern | [`Beluga/Patterns.lean :: availabilityPattern`](BlockSynchroniser/Beluga/Patterns.lean#L38) | ✅ — strong-link only. |
| §4.4 — Certificate pattern | [`Beluga/Patterns.lean :: certificatePattern`](BlockSynchroniser/Beluga/Patterns.lean#L49) | ✅ |
| §4.4 — `available` / `certified` | [`Beluga/Patterns.lean`](BlockSynchroniser/Beluga/Patterns.lean#L54) | ✅ |
| §4.4 — Uniqueness consequence ("for any validator and round, at most one block can become certified") | [`Beluga/Patterns.lean :: certified_unique`](BlockSynchroniser/Beluga/Patterns.lean#L152) | ✅ — uses the BFT scope-pinning of finding F-2 and the cross-block non-equivocation of finding F-3(a). |

### §5 — Beluga's main theorems

The §5 layer lives in [`Beluga/Theorems.lean`](BlockSynchroniser/Beluga/Theorems.lean)
and is stated against the network-aware trace
`networkBelugaTraceWithPull`. The protocol layer (state, step,
fairness derivation, named liveness primitives) lives in
[`Beluga/Network.lean`](BlockSynchroniser/Beluga/Network.lean).

| Paper | Code | Status |
|---|---|---|
| §5 — **Lemma 1** — after GST, all honest validators reach the same round within 3Δ | [`Beluga/Theorems.lean :: lemma1_honest_round_entry`](BlockSynchroniser/Beluga/Theorems.lean) | ✅ — weakened to the lockstep-progress form (the strict same-round form is unprovable from the cited assumptions; finding F-1b). |
| §5 — **Lemma 2** — round-to-round latency ≤ 3Δ in the happy case | [`Beluga/Theorems.lean :: lemma2_round_latency`](BlockSynchroniser/Beluga/Theorems.lean) | ✅ |
| §5 — **Theorem 1** — Beluga ⊨ Block availability | [`Beluga/Theorems.lean :: network_theorem1_block_availability_withPull`](BlockSynchroniser/Beluga/Theorems.lean) | ✅ |
| §5 — **Theorem 2** — Beluga ⊨ Causal availability | [`Beluga/Theorems.lean :: network_theorem2_causal_availability_withPull`](BlockSynchroniser/Beluga/Theorems.lean) | ✅ |
| §5 — **Theorem 3** — Beluga ⊨ Round-Progression | [`Beluga/Theorems.lean :: network_theorem3_round_progression_withPull`](BlockSynchroniser/Beluga/Theorems.lean) | ✅ |
| §5 — **Theorem 4** — Beluga ⊨ Round-Termination | [`Beluga/Theorems.lean :: network_theorem4_round_termination_proved`](BlockSynchroniser/Beluga/Theorems.lean) | ✅ |
| §5 corollary — Beluga is a block synchronizer (T1∧T2∧T3∧T4) | [`Beluga/Theorems.lean :: beluga_isBlockSynchronizer`](BlockSynchroniser/Beluga/Theorems.lean) | ✅ |
| Pull mechanism (paper §4.3) explicit modelling | [`Beluga/Network.lean`](BlockSynchroniser/Beluga/Network.lean) | ✅ |
| Paper-stated liveness assumptions of §2 + §4.2 + §4.3 bundled (`BelugaWithPullFairness`) | [`Beluga/Theorems.lean :: BelugaWithPullFairness`](BlockSynchroniser/Beluga/Theorems.lean) | ✅ — surfaces the per-action and pull-channel liveness conclusions the paper's §5 prose uses silently (finding F-1). |

### Appendix C — Performance bounds

| Paper | Code | Status |
|---|---|---|
| **Assumption 1 — latency triangle** (honest-to-honest direct delivery is faster than any relay through an intermediate validator) | [`Beluga/PerformanceLemmas.lean :: LatencyTriangle`](BlockSynchroniser/Beluga/PerformanceLemmas.lean#L46) | ✅ Definition. Adapted to the trace model: post-GST, if all honest validators are at round `r` they all reach `r+1` within `Δ`. Used as a hypothesis to **L4** and **L5** below. |
| **Lemma 3** — honest validators are not blamed (post-GST) | [`Beluga/PerformanceLemmas.lean :: lemma3_honest_not_blamed`](BlockSynchroniser/Beluga/PerformanceLemmas.lean#L64) | ✅ proved |
| **Lemma 4** — round latency Δ when honest reputations dominate | [`Beluga/PerformanceLemmas.lean :: lemma4_round_latency_delta`](BlockSynchroniser/Beluga/PerformanceLemmas.lean#L110) | ✅ Takes `LatencyTriangle` (Assumption 1, see above) as an explicit hypothesis |
| **Lemma 5** — round latency 2Δ-or-blame (deterministic part) | [`Beluga/PerformanceLemmas.lean :: lemma5_round_latency_or_blamed`](BlockSynchroniser/Beluga/PerformanceLemmas.lean#L154) | ✅ Same `LatencyTriangle` hypothesis as L4 |
| **Lemmas 6, 7** + **Theorem 5** — expected-latency bounds | — | ⊘ Probabilistic; genuinely out of scope (would need a probability framework) |

### Appendix D — Mysticeti-Beluga (Phase 6)

| Paper | Code | Status |
|---|---|---|
| D.1.1 — Direct / indirect decision rules | [`Mysticeti/Consensus.lean :: directDecide` / `indirectDecideStep`](BlockSynchroniser/Mysticeti/Consensus.lean#L100) | ✅ |
| D.1.1 — Skip pattern / certificate pattern (at next round) | [`Mysticeti/Consensus.lean :: skipPattern` / `certificatePatternAt`](BlockSynchroniser/Mysticeti/Consensus.lean#L44) | ✅ |
| D.1.2 — Round-robin leader schedule | [`Mysticeti/Consensus.lean :: leaderOf` / `isLeaderBlock`](BlockSynchroniser/Mysticeti/Consensus.lean#L27) | ✅ |
| **Lemma 8** — leader block referenced next round (after GST) | [`Mysticeti/Liveness.lean :: lemma8_leader_referenced`](BlockSynchroniser/Mysticeti/Liveness.lean#L360) | ◐ Top-level composition closed; transitively gated on the bundle's `honest_ref_leader` conjunct |
| **Lemma 9** — honest validators create certificate for honest leader | [`Mysticeti/Liveness.lean :: lemma9_honest_certificate`](BlockSynchroniser/Mysticeti/Liveness.lean#L420) | ◐ Top-level composition closed; transitively gated on the bundle's `honest_certify_leader` conjunct |
| **Lemma 10** — round-robin pigeonhole (3 consecutive honest leaders in any 3f+3 window) | [`Mysticeti/Safety.lean :: lemma10_round_robin_pigeonhole`](BlockSynchroniser/Mysticeti/Safety.lean#L111) | ✅ proved (takes `n=3f+1`, honest-count = 2f+1, validator-IDs-contiguous; the last is finding F-8). |
| **Lemma 11** — undecided leader block eventually decided | [`Mysticeti/Liveness.lean :: lemma11_eventual_decision`](BlockSynchroniser/Mysticeti/Liveness.lean#L522) | ◐ Top-level composition closed; gated on the bundle's `three_consec_commit` + `backward_induction` conjuncts |
| **Lemma 12** — block referenced by 2f+1 ⇒ honest validators output `block_accept` | [`Mysticeti/Liveness.lean :: lemma12_referenced_accepted`](BlockSynchroniser/Mysticeti/Liveness.lean#L660) | ◐ Top-level composition closed; takes `hids : ValidIds system` + the `MysticetiPostGSTLiveness` bundle hypotheses (`hN`, `hHonest`, `h_ids`); the bundle's `byz_bound` conjunct is now sorry-free (Aristotle round `2300aa5f`); gated on the bundle's `block_pull_liveness` conjunct |
| **Lemma 13** — certificate persistence across rounds | [`Mysticeti/Safety.lean :: lemma13_cert_persistence`](BlockSynchroniser/Mysticeti/Safety.lean#L237) | ✅ proved via paper §D.3 quorum-intersection argument; uses the new `AdmissionWellFormed` trace invariant (a *theorem* about `belugaTrace`, not a hypothesis) plus `h_honest_unique` (standard BFT no-equivocation). Closes F-5 item 1. **belugaTrace specialisation** [`lemma13_cert_persistence_belugaTrace`](BlockSynchroniser/Mysticeti/Safety.lean#L581) discharges all four protocol-invariant hypotheses from `MysticetiSafetyInv`. |
| **Lemma 14** — no honest validator skips a directly-committed leader | [`Mysticeti/Safety.lean :: lemma14_no_skip`](BlockSynchroniser/Mysticeti/Safety.lean#L336) | ✅ proved. |
| **Lemma 15** — at most one certified leader per round | [`Mysticeti/Safety.lean :: lemma15_unique_cert`](BlockSynchroniser/Mysticeti/Safety.lean#L376) | ✅ specialization of `certified_unique`; threads through the same BFT side conditions. **belugaTrace specialisation** [`lemma15_unique_cert_belugaTrace`](BlockSynchroniser/Mysticeti/Safety.lean#L611) discharges the protocol-invariant hypotheses from `MysticetiSafetyInv`. |
| **Lemma 16** — consistent leader-status decision across honest validators | [`Mysticeti/Safety.lean :: lemma16_consistent_status`](BlockSynchroniser/Mysticeti/Safety.lean#L445) | ✅ proved with `h_view_traceback` hypothesis; see finding F-5. |
| **Theorem 6** — Mysticeti-Beluga consensus liveness | [`Mysticeti/Liveness.lean :: theorem6_consensus_liveness`](BlockSynchroniser/Mysticeti/Liveness.lean#L768) | ◐ Top-level proof closed; gated on 8 of 12 conjuncts of the `MysticetiPostGSTLiveness` bundle (paper §D.2 deep liveness properties). The bundle's system-level scaffolding (`hN`/`hHonest`/`h_ids`) and `byz_bound` conjunct were closed by Aristotle round `2300aa5f`; the 8 deep conjuncts (`honest_round_entry`, `leader_propose`, `honest_ref_leader`, `honest_certify_leader`, `three_consec_commit`, `backward_induction`, `block_pull_liveness`, `honest_eventually_accepts`) await further narrow rounds. |
| **Theorem 7** — Mysticeti-Beluga consensus safety | [`Mysticeti/Safety.lean :: theorem7_consensus_safety`](BlockSynchroniser/Mysticeti/Safety.lean#L517) | ⚠️ proved with `h_decision_complete` + `h_order_from_view` hypotheses but **finding F-7 flags both as unfaithful** to the paper (liveness ingredient + modeling artifact); restatement pending. |
| **MysticetiSafetyInv bundle** for `belugaTrace` (folds `h_admission`, `h_honest_unique`, `h_no_eq`, `h_authors_valid`) | [`Mysticeti/SafetyInvariant.lean :: belugaTrace_satisfies_mysticetiSafetyInv`](BlockSynchroniser/Mysticeti/SafetyInvariant.lean#L243) | ✅ all four conjuncts proved (admission via `belugaTrace_admissionWellFormed`; uniqueByAuthorRound + noEquivocation from `BlockInv`; `authorsValid` closed in Aristotle round `c2ca4a2e` via a joint blocks-+-validator-IDs inductive carrier). The bundle is the foundation for `lemma13_cert_persistence_belugaTrace` and `lemma15_unique_cert_belugaTrace`. |

## Not in the paper — internal validation

The `golden_*`, `realizable_*`, and `not_*_emptyTrace` lemmas in
[`Validation.lean`](BlockSynchroniser/Validation.lean#L57) **are not paper
results.** They are sanity checks demonstrating that our Lean version of
each Definition-1 property is satisfiable / falsifiable by concrete traces
(non-vacuity validation). The opening comment of `Validation.lean` spells
out the distinction.

All four `golden_*` theorems are fully proved; the realizability
and anti-witness lemmas are also closed.

## Refinement chain and reusable trace invariants

Two properties of the proof architecture are worth calling out
explicitly because both are load-bearing for everything downstream
and neither falls out of any single theorem statement.

### 1. Executable-spec refinement is closed

Our paper §5 theorems (T1–T4 and the corollary
`belugaTrace_isBlockSynchronizer`) are stated against the executable
trace [`belugaTrace`](BlockSynchroniser/Beluga/Protocol.lean), but
the [Definition-1 properties they reference](BlockSynchroniser/Properties.lean)
are stated against the abstract relational semantics
[`HonestStep`](BlockSynchroniser/Trace.lean). Without a refinement
proof, the theorems would be claims about a Lean function with no
established connection to the paper's abstract behavior.

That bridge is
[`step_refines_HonestStep`](BlockSynchroniser/Beluga/Protocol.lean):
every executable `step system s` move corresponds to a `HonestStep`
in the abstract semantics. Once it is proved, every property
satisfied by all `HonestStep`-respecting traces lifts automatically
to `belugaTrace`.

The transitive closure of `step_refines_HonestStep` was gated on a
single trace-level obligation, `causal_history_of_find_none`: if a
block is not present in the trace by digest, then no block in the
trace causally references it. This cannot be proved one-step; it
requires an inductive invariant about *every* state reachable in the
trace. Closing it (Aristotle round `3f6cf619`) closed the entire
refinement chain.

### 2. `BlockInv → AcceptInv → CausallyClosed` is a vocabulary, not just plumbing

The compound trace-invariant carrier introduced to close
`causal_history_of_find_none` ([`Beluga/Protocol.lean`](BlockSynchroniser/Beluga/Protocol.lean))
has three stages:

| Invariant | What it carries |
|---|---|
| `BlockInv` | every block has canonical digest (`B.d = digest system B.r B.author`); every block has a propose op; `(author, round)` propose-uniqueness; author bounds |
| `AcceptInv` | causal closure of acceptance (accepted block ⇒ accepted parents); `acceptedBlockExists` |
| `CausallyClosed` | the consequence consumed by `step_refines_HonestStep` |

These invariants were initially needed only to close the refinement.
But the same vocabulary has since been independently picked up by
two other proofs that have no direct connection to refinement:

- [`Beluga/Order.lean`](BlockSynchroniser/Beluga/Order.lean) —
  finding **F-7(b)** is closed by defining
  `belugaTransactionOrder` as a concrete function and proving
  `accepted_implies_in_belugaTransactionOrder`. The proof uses
  `BlockInv.canonical` + `digest_injective` for *block uniqueness
  by digest* — the helper lemma
  `block_unique_by_digest_in_trace` is one direct corollary of
  `BlockInv`.
- [`Mysticeti/SafetyInvariant.lean`](BlockSynchroniser/Mysticeti/SafetyInvariant.lean)
  — three of four conjuncts of the new `MysticetiSafetyInv` bundle
  (`uniqueByAuthorRound` and `noEquivocation` directly,
  `admission` via `belugaTrace_admissionWellFormed`) are
  sorry-free derivations from `BlockInv.hasPropose` +
  `BlockInv.uniquePropose`. No new induction was needed; the
  carrier already carried the right facts.

In both cases the conjuncts of `BlockInv` were *exactly* the
inductive vocabulary the proof needed. The carrier earned its
keep beyond its original purpose. The practical takeaway: when
you invest in stating the right inductive invariant once,
downstream proofs that need substructures of it are short and
structural rather than re-deriving the carrier.

### Implication for future work

Future work that needs structural facts about `belugaTrace` —
e.g., closing `h_authors_valid` (the remaining
`MysticetiSafetyInv` sorry), discharging the BFT-bound assumptions
in Mysticeti's `Liveness.lean`, or strengthening Mysticeti's
`Safety.lean` view-related hypotheses — should look first at
whether the fact is a corollary of (or natural extension to) the
existing invariant chain, rather than introducing a parallel
carrier. New conjuncts can be added to `BlockInv` /
`MysticetiSafetyInv` so long as they remain inductively
preserved by `step`.

## Notes on paper consistency

> **Paper-side findings live in [`docs/mechanization-findings.md`](docs/mechanization-findings.md)**
> (F-1 / F-1a through F-8 plus F-11: scheduler-fairness for L1/L2 in
> its lockstep form, T7's safety/liveness boundary, surfaced protocol
> invariants, quorum-size pinning, block-digest determinism, etc.).
> That file uses paper terminology only and is the working list of
> edits we plan to propose to the paper authors.
>
> The notes below cover only **Lean-side modeling decisions** — items
> that don't surface a paper concern but explain how our formalization
> structures things differently from the paper's prose.

### Lean-side modeling notes

- **`signature` field on `Block` omitted** (paper §2.1). The paper's
  block carries six fields `(r, d, author, parents, payload, signature)`;
  our [`Block.lean :: Block`](BlockSynchroniser/Block.lean#L22) carries
  the first five. Signature semantics are not invoked by any theorem in
  the scope we formalize — the abstract block synchronizer (and every
  paper theorem we target) treats Byzantine behavior adversarially via
  the honest/Byzantine partition rather than via signature-based
  attribution. Adding `signature` would only add data fields and a
  `verify` predicate that no proof references.

- **`BelugaState.WellFormed system s`** (on
  `Beluga/Protocol.lean :: step_refines_HonestStep`). Every entry in
  `s.validators` is registered in `system.validators`. The paper conflates
  state's validators with the system's validators by construction; our
  `BelugaState` is a separate data type that doesn't enforce this, so we
  surface it as an explicit hypothesis. Pure modeling artifact — no paper
  concern.

- **Lemma 5 split (Appendix C).** The paper's Lemma 5 mixes "expected
  latency" with the deterministic "or at least one malicious validator
  is blamed" disjunction. The expected side is probabilistic and out of
  scope; we formalize only the deterministic disjunct as
  `lemma5_round_latency_or_blamed`. This is a Lean-side decomposition
  decision, not a paper finding.

- **§5 hypothesis set: `BelugaWithPullFairness` bundle.**
  L1, L2, T1, T2, T3, T4 (and the corollary
  `beluga_isBlockSynchronizer`) all consume the single bundle
  `Network.BelugaWithPullFairness system time` (seven-field record
  covering paper §2 + §4.2 + §4.3 post-GST liveness primitives:
  `timeMonotone`, `timeUnbounded`, `networkDelivery`
  (`NetworkDeliveryWithPull`, paper §2 `Δ`-delivery),
  `actionScheduling` (`ActionSchedulingWithPull`, paper §4.2
  round-advance), `boundedRoundSpread` (paper §4.2 protocol
  synchronization), `acceptScheduling` (paper §4.2 accept-action
  liveness), `inPoolDelivery` (`NetworkInPoolDeliveryWithPull`,
  paper §4.3 universal in-pool delivery — push ∪ pull)).
  `EventualCausalAcceptance` and `EventualRoundAcceptance` are
  derived theorems, not axioms.

Real paper-side concerns (missing assumptions, scope ambiguities,
implicit invariants) are recorded in
[`docs/mechanization-findings.md`](docs/mechanization-findings.md).

## Where to look

| | |
|---|---|
| Mechanization findings (paper-side log) | [docs/mechanization-findings.md](docs/mechanization-findings.md) |
| Why per-action liveness is needed and ImPoA does not substitute | [docs/paper-feedback-impoa-vs-fairness.md](docs/paper-feedback-impoa-vs-fairness.md) |
| Recommended paper additions / restatements | [docs/paper-additions-stage2.md](docs/paper-additions-stage2.md) |
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
│   │   ├── Network.lean        ← network-aware §4 protocol layer
│   │   │                          (NetworkState, networkStep,
│   │   │                          networkStepWithPull, fairness
│   │   │                          derivation, paper liveness primitives)
│   │   ├── Examples.lean       ← system4, run, #eval smoke tests
│   │   └── Theorems.lean       ← §5 paper layer: BelugaWithPullFairness,
│   │                              L1, L2, T1–T4, beluga_isBlockSynchronizer
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
honest system (see [`BlockSynchroniser/Beluga/Examples.lean :: system4`](BlockSynchroniser/Beluga/Examples.lean#L17))
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

`#eval` smoke tests in [`Examples.lean`](BlockSynchroniser/Beluga/Examples.lean#L17)
exercise:

- `(run n).emittedOperations.length` — total ops after `n` steps.
- `proposersFor (run n) r` — distinct round-`r` proposers.
- `reprLog (run n)` — pretty-printed op log.

The schedule is round-robin: each step scans validators in id order and
applies the first available action (priority: propose → accept → store →
advance). vid 0 exhausts its actions before vid 1 takes over, then vid 2,
then vid 3.
