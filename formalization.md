# Formalization overview

Lean 4 formalization of [*Beluga: Block Synchronization for BFT Consensus
Protocols*](docs/round-01/Block_Sync_Project.pdf).

## Paper → code map

The single source of truth for which paper item lives where in this repo.
Status: ✅ done · ◐ in progress · ☐ planned · ⊘ out of scope · ⏸ deferred.

### §2 — Network model and synchronizer abstraction

| Paper | Code | Status |
|---|---|---|
| §2 — Network model (`n`, `f`, `k`, `GST`, `Δ`) | [`System.lean :: BlockSynchroniserSystem`](BlockSynchroniser/System.lean#L22) | ✅ |
| §2 — Honest / Byzantine partition | [`System.lean :: isHonest` / `isByzantine`](BlockSynchroniser/System.lean#L58) | ✅ |
| §2.1 — Block structure (`r, d, author, parents, payload, signature`) | [`Block.lean :: Block`](BlockSynchroniser/Block.lean#L22) | ✅ — signature field omitted (see note below); digest determinism is carried as a side condition rather than baked into the field itself. |
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
| §4.2 — Reputation mechanism (increase / decrease rules; Figure 8 lines 23–32) | [`Beluga/Reputation.lean`](BlockSynchroniser/Beluga/Reputation.lean#L23) | ✅ |
| §4.2 — Admission Control + parent selection (Figure 8 lines 14–17 + round-advancement rule (i)) | [`Beluga/AdmissionControl.lean`](BlockSynchroniser/Beluga/AdmissionControl.lean#L60) | ✅ |
| §4.3 — ImPoA (implicit proof-of-availability) + live/bulk classification | [`Beluga/Pull.lean`](BlockSynchroniser/Beluga/Pull.lean#L30) | ✅ — strong-link only; weak-link inclusion deferred. |
| §4 — `BelugaState`, `BelugaValidator`, `ReputationTable` | [`Beluga/State.lean`](BlockSynchroniser/Beluga/State.lean#L97) | ✅ |
| §4 — Protocol semantics: `HonestStep` (relational) + executable `step` + `belugaTrace` | [`Beluga/Protocol.lean`](BlockSynchroniser/Beluga/Protocol.lean#L185) | ✅ |
| §4 — Executable demos (`#eval`, `lake exe blocksynchroniser`) | [`Beluga/Examples.lean`](BlockSynchroniser/Beluga/Examples.lean#L17) | ✅ |
| §4.3 — Random pull complexity bound (`O(1)`) | — | ⊘ probabilistic |
| §4.4 — Availability pattern | [`Beluga/Patterns.lean :: availabilityPattern`](BlockSynchroniser/Beluga/Patterns.lean#L38) | ✅ — strong-link only. |
| §4.4 — Certificate pattern | [`Beluga/Patterns.lean :: certificatePattern`](BlockSynchroniser/Beluga/Patterns.lean#L49) | ✅ |
| §4.4 — `available` / `certified` | [`Beluga/Patterns.lean`](BlockSynchroniser/Beluga/Patterns.lean#L54) | ✅ |
| §4.4 — Uniqueness consequence ("for any validator and round, at most one block can become certified") | [`Beluga/Patterns.lean :: certified_unique`](BlockSynchroniser/Beluga/Patterns.lean#L152) | ✅ — uses the BFT scope-pinning `n = 3f + 1` and a cross-block honest non-equivocation form. |

### §5 — Beluga's main theorems

The §5 layer lives in [`Beluga/Theorems.lean`](BlockSynchroniser/Beluga/Theorems.lean)
and is stated against the network-aware trace
`networkBelugaTraceWithPull`. The protocol layer (state, step,
fairness derivation, named liveness primitives) lives in
[`Beluga/Network.lean`](BlockSynchroniser/Beluga/Network.lean).

| Paper | Code | Status |
|---|---|---|
| §5 — **Lemma 1** — after GST, if `r` is the highest round any honest validator is in at time `t`, every honest validator is at round `≥ r` by some step within `4Δ` | [`Beluga/Theorems.lean :: lemma1_honest_round_entry`](BlockSynchroniser/Beluga/Theorems.lean#L1506) | ✅ — proved against `BelugaPartialSynchrony` (the paper-faithful event-triggered bundle). |
| §5 — **Theorem 1** — Beluga ⊨ Block availability | [`Beluga/Theorems.lean :: network_theorem1_block_availability_withPull`](BlockSynchroniser/Beluga/Theorems.lean#L1856) | ✅ |
| §5 — **Theorem 2** — Beluga ⊨ Causal availability | [`Beluga/Theorems.lean :: network_theorem2_causal_availability_withPull`](BlockSynchroniser/Beluga/Theorems.lean#L2099) | ✅ |
| §5 — **Theorem 3** — Beluga ⊨ Round-Progression | [`Beluga/Theorems.lean :: network_theorem3_round_progression_withPull`](BlockSynchroniser/Beluga/Theorems.lean#L1923) | ✅ |
| §5 — **Theorem 4** — Beluga ⊨ Round-Termination | [`Beluga/Theorems.lean :: network_theorem4_round_termination_proved`](BlockSynchroniser/Beluga/Theorems.lean#L1805) | ✅ |
| §5 corollary — Beluga is a block synchronizer (T1∧T2∧T3∧T4) | [`Beluga/Theorems.lean :: beluga_isBlockSynchronizer`](BlockSynchroniser/Beluga/Theorems.lean#L2140) | ✅ |
| Pull mechanism (paper §4.3) explicit modelling | [`Beluga/Network.lean`](BlockSynchroniser/Beluga/Network.lean#L90) | ✅ |
| Paper-stated liveness assumptions of §2 + §4.2 + §4.3, event-triggered form (`BelugaPartialSynchrony`) | [`Beluga/Theorems.lean :: BelugaPartialSynchrony`](BlockSynchroniser/Beluga/Theorems.lean#L68) | ✅ — packages clock, push delivery, in-pool delivery, accept-action liveness, gap-1 protocol synchronization, and the §4.2 rule (i)/(iii) catch-up primitive. |
| Strengthened bundle for the §5 theorems (`BelugaWithPullFairness extends BelugaPartialSynchrony`) | [`Beluga/Theorems.lean :: BelugaWithPullFairness`](BlockSynchroniser/Beluga/Theorems.lean#L98) | ✅ — adds `TimeoutAdvanceWithPull` (paper §4.2 rule (ii), per-round timeout `T_rd = 5Δ`). T1–T4 consume this to drive unbounded round progression; every assumption now corresponds to a paper-stated primitive. |

### Appendix C — Performance bounds

| Paper | Code | Status |
|---|---|---|
| **Assumption 1 — latency triangle** | [`Beluga/PerformanceLemmas.lean :: LatencyTriangle`](BlockSynchroniser/Beluga/PerformanceLemmas.lean#L40) | ✅ — used as an explicit hypothesis on L4 and L5. |
| **Lemma 3** — honest validators are not blamed (post-GST) | [`Beluga/PerformanceLemmas.lean :: lemma3_honest_not_blamed`](BlockSynchroniser/Beluga/PerformanceLemmas.lean#L58) | ✅ |
| **Lemma 4** — round latency Δ when honest reputations dominate | [`Beluga/PerformanceLemmas.lean :: lemma4_round_latency_delta`](BlockSynchroniser/Beluga/PerformanceLemmas.lean#L102) | ✅ |
| **Lemma 5** — round latency 2Δ-or-blame (deterministic part) | [`Beluga/PerformanceLemmas.lean :: lemma5_round_latency_or_blamed`](BlockSynchroniser/Beluga/PerformanceLemmas.lean#L145) | ✅ |
| **Lemmas 6, 7** + **Theorem 5** — expected-latency bounds | — | ⊘ — probabilistic; out of scope. |

### Appendix D — Mysticeti-Beluga

| Paper | Code | Status |
|---|---|---|
| D.1.1 — Direct / indirect decision rules | [`Mysticeti/Consensus.lean :: directDecide` / `indirectDecideStep`](BlockSynchroniser/Mysticeti/Consensus.lean#L100) | ✅ |
| D.1.1 — Skip pattern / certificate pattern (at next round) | [`Mysticeti/Consensus.lean :: skipPattern` / `certificatePatternAt`](BlockSynchroniser/Mysticeti/Consensus.lean#L44) | ✅ |
| D.1.2 — Round-robin leader schedule | [`Mysticeti/Consensus.lean :: leaderOf` / `isLeaderBlock`](BlockSynchroniser/Mysticeti/Consensus.lean#L27) | ✅ |
| **Lemma 8** — leader block referenced next round (after GST) | [`Mysticeti/Liveness.lean :: lemma8_leader_referenced`](BlockSynchroniser/Mysticeti/Liveness.lean#L357) | ◐ — top-level composition closed; gated on the §D.2 liveness primitive `honest_ref_leader`. |
| **Lemma 9** — honest validators create certificate for honest leader | [`Mysticeti/Liveness.lean :: lemma9_honest_certificate`](BlockSynchroniser/Mysticeti/Liveness.lean#L417) | ◐ — top-level closed; gated on the §D.2 primitive `honest_certify_leader`. |
| **Lemma 10** — round-robin pigeonhole (3 consecutive honest leaders in any 3f+3 window) | [`Mysticeti/Safety.lean :: lemma10_round_robin_pigeonhole`](BlockSynchroniser/Mysticeti/Safety.lean#L108) | ✅ — relies on the contiguous validator-IDs assumption (`{v_0, …, v_{n-1}}`). |
| **Lemma 11** — undecided leader block eventually decided | [`Mysticeti/Liveness.lean :: lemma11_eventual_decision`](BlockSynchroniser/Mysticeti/Liveness.lean#L519) | ◐ — top-level closed; gated on the §D.2 primitives `three_consec_commit` + `backward_induction`. |
| **Lemma 12** — block referenced by 2f+1 ⇒ honest validators output `block_accept` | [`Mysticeti/Liveness.lean :: lemma12_referenced_accepted`](BlockSynchroniser/Mysticeti/Liveness.lean#L657) | ◐ — top-level closed; gated on the §D.2 primitive `block_pull_liveness`. |
| **Lemma 13** — certificate persistence across rounds | [`Mysticeti/Safety.lean :: lemma13_cert_persistence`](BlockSynchroniser/Mysticeti/Safety.lean#L233) | ✅ — the four DAG-level invariants (admission well-formedness, author-round uniqueness, no-equivocation in parents, authors-are-registered) are derived as theorems for `belugaTrace`. |
| **Lemma 14** — no honest validator skips a directly-committed leader | [`Mysticeti/Safety.lean :: lemma14_no_skip`](BlockSynchroniser/Mysticeti/Safety.lean#L332) | ✅ |
| **Lemma 15** — at most one certified leader per round | [`Mysticeti/Safety.lean :: lemma15_unique_cert`](BlockSynchroniser/Mysticeti/Safety.lean#L372) | ✅ |
| **Lemma 16** — consistent leader-status decision across honest validators | [`Mysticeti/Safety.lean :: lemma16_consistent_status`](BlockSynchroniser/Mysticeti/Safety.lean#L440) | ✅ — takes a view-traceback hypothesis. |
| **Theorem 6** — Mysticeti-Beluga consensus liveness | [`Mysticeti/Liveness.lean :: theorem6_consensus_liveness`](BlockSynchroniser/Mysticeti/Liveness.lean#L765) | ◐ — top-level closed; gated on 8 of the §D.2 deep liveness primitives. |
| **Theorem 7** — Mysticeti-Beluga consensus safety | [`Mysticeti/Safety.lean :: theorem7_consensus_safety`](BlockSynchroniser/Mysticeti/Safety.lean#L511) | ✅ — paper §D.3 restates T7 as prefix-consistency of ordered transaction sequences; mechanized verbatim. |
| Mysticeti safety invariants for `belugaTrace` | [`Mysticeti/SafetyInvariant.lean :: belugaTrace_satisfies_mysticetiSafetyInv`](BlockSynchroniser/Mysticeti/SafetyInvariant.lean#L249) | ✅ — discharges the four DAG-invariant hypotheses of L13/L15 (admission well-formedness, author-round uniqueness, no-equivocation in parents, authors-are-registered). |

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

The transitive closure of `step_refines_HonestStep` rests on a
single trace-level obligation, `causal_history_of_find_none`: if
a block is not present in the trace by digest, then no block in
the trace causally references it. This cannot be proved one-step;
it requires an inductive invariant about *every* state reachable
in the trace. Discharging it closes the entire refinement chain.

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

## Lean-side modeling notes

The notes below describe how our formalization structures things
differently from the paper's prose. They do not by themselves
imply a paper concern; they record places where the Lean encoding
makes an assumption explicit that the paper leaves implicit, or
where we model a paper datatype slightly differently for
mechanization-related reasons.

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

- **§5 hypothesis sets: `BelugaPartialSynchrony` and `BelugaWithPullFairness`.**
  Lemma 1 consumes the weaker `Network.BelugaPartialSynchrony system time`
  bundle (seven-field record packaging the paper's §2 + §4.2 + §4.3
  post-GST liveness in event-triggered form: `timeMonotone`,
  `timeUnbounded`, `networkDelivery` (`NetworkDeliveryWithPull`,
  paper §2 `Δ`-delivery), `boundedRoundSpread` (paper §4.2
  protocol synchronization, gap ≤ 1), `acceptScheduling` (paper
  §4.2 accept-action liveness), `inPoolDelivery`
  (`NetworkInPoolDeliveryWithPull`, paper §4.3 universal in-pool
  delivery — push ∪ pull), `catchUpLiveness` (paper §4.2 rules
  (i)/(iii) catch-up to a leader within `4Δ`)).

  `BelugaWithPullFairness` extends `BelugaPartialSynchrony` with
  `timeoutAdvance` (`TimeoutAdvanceWithPull`) — paper §4.2 rule (ii),
  the per-round timeout `T_rd = 5Δ`. T1–T4 consume this to drive
  unbounded round progression; every field of every bundle
  corresponds to a paper-stated or paper-implicit primitive.
  `EventualCausalAcceptance` and `EventualRoundAcceptance` are
  derived theorems, not axioms.

## Where to look

| | |
|---|---|
| Mechanization findings, round 1 | [docs/round-01/mechanization-findings.md](docs/round-01/mechanization-findings.md) |
| Mechanization findings, round 2 | [docs/round-02/round-02-findings.md](docs/round-02/round-02-findings.md) |
| Why per-action liveness is needed and ImPoA does not substitute | [docs/round-01/paper-feedback-impoa-vs-fairness.md](docs/round-01/paper-feedback-impoa-vs-fairness.md) |
| Recommended paper additions, round 1 (Stage 1 + Stage 2) | [docs/round-01/paper-additions-stage1.md](docs/round-01/paper-additions-stage1.md), [docs/round-01/paper-additions-stage2.md](docs/round-01/paper-additions-stage2.md) |
| Recommended paper additions, round 2 (Stage 3) | [docs/round-02/paper-additions-stage3.md](docs/round-02/paper-additions-stage3.md) |
| Per-stage changelog | [changelogs/](changelogs/) |
| The original paper (round 1) | [docs/round-01/Block_Sync_Project.pdf](docs/round-01/Block_Sync_Project.pdf) |
| The revised paper (round 2) | [docs/round-02/Block_Sync_Project2.pdf](docs/round-02/Block_Sync_Project2.pdf) |

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

Toolchain pinned to `leanprover/lean4:v4.28.0`.

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
