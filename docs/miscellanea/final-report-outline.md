# Final report — outline draft

Skeleton for the eventual report on this formalization. Captures
contributions, methodology, attribution, and open work. Filled in as
the project lands more proofs.

## Title

*Beluga in Lean 4: A Formalization of Block-Synchronizer Properties for
Byzantine Fault-Tolerant Consensus*

(or some variant — final wording TBD)

## Abstract

We present a Lean 4 formalization of the abstract block-synchronizer
specification (paper §2.1, Definition 1) and the Beluga protocol that
realizes it (paper §4–§5), together with the safety/liveness reasoning
for Mysticeti-Beluga consensus (paper Appendix D). The formalization
combines hand proofs (definitions, the Definition-1 specifications,
non-vacuity validation, infrastructure lemmas) with proofs delegated to
Aristotle (Harmonic), an LLM-driven Lean prover, for the substantive
theorems where the bottleneck is Lean tactic plumbing rather than
mathematical reasoning. We articulate the *math tactical wall* concept
guiding our human/AI division of labor.

## 1. Introduction

- Beluga: quick paper summary.
- Why formalize: gives precise, machine-checked statements of the
  block-synchronizer abstraction and its theorems.
- Methodology preview: hand-prove definitions and validation; delegate
  substantive proofs to Aristotle when Lean plumbing dominates.

## 2. The abstraction (paper §2.1)

- Network model, threat model.
- Block structure, synchronizer interface, causal history.
- **Definition 1 — the four properties**:
  - Round-Progression
  - Round-Termination
  - Block availability
  - Causal availability
- Lean encoding: `Properties.lean`.
- Key design decisions:
  - `Trace = Nat → S` indexed by step number.
  - `SystemState` typeclass for state extensibility.
  - Inductive `Reaches` for causal closure (vs. list-based paths).
  - Honest/Byzantine binary partition.

## 3. Validation (non-vacuity)

The four Definition-1 properties have shape `P → ∃ Q` and admit the
empty trace as a vacuous model. We address this with three layers
(`Validation.lean`):

- **Layer A — `goldenTrace`**: a concrete honest-synchronous trace
  satisfies all four properties. Proved by Aristotle.
- **Layer B — realizability**: each antecedent is reachable in *some*
  trace. Hand-proved.
- **Layer C — anti-witnesses**: empty trace fails at least
  `RoundProgression` and `RoundTermination`. Hand-proved.

Discuss: how this caught (or could catch) over-permissive specs.

## 4. The Beluga protocol (paper §4)

### 4.1 Block extensions

- `BelugaBlock`: extends `Block` with `weaklinks`, `watermark`,
  `ancestors`. `BlockExt.lean`.

### 4.2 Reputation and admission control

- `ReputationTable`, `updateScoreWithWatermarks`, `reputationThreshold`.
- `acParentSelection`, `canAdvanceByQuorum`. `Reputation.lean` +
  `AdmissionControl.lean`.

### 4.3 ImPoA-based hybrid pull

- `implicitlyAvailable`, `isLive` / `isBulk` / `classifyMissing`.
- `isAcceptableImPoA`. `Pull.lean`.

### 4.4 Block patterns

- `availabilityPattern`, `certificatePattern`, `available`, `certified`.
- `certified_unique` (paper §4.4 informal uniqueness). `Patterns.lean`.

### 4.5 Protocol semantics

- `HonestStep` relational small-step semantics with five cases (4
  honest + Byzantine).
- `step` executable round-robin scheduler.
- `belugaTrace` — iterated `step` from `BelugaState.init`.
- Refinement: `step_refines_HonestStep`. `Protocol.lean`.
- Runnable demo: `lake exe blocksynchroniser`. `Examples.lean` +
  `Main.lean`.

## 5. Main theorems (paper §5)

For each, a precise Lean statement plus paper-derived proof sketch:

- **Lemma 1**: 3Δ post-GST round entry. Timing via `TimeMap` +
  `PartiallySynchronous`.
- **Lemma 2**: 3Δ round-to-round latency.
- **Theorem 1**: Beluga ⊨ Block availability.
- **Theorem 2**: Beluga ⊨ Causal availability.
- **Theorem 3**: Beluga ⊨ Round-Progression.
- **Theorem 4**: Beluga ⊨ Round-Termination.

`Beluga/Theorems.lean`.

## 6. Mysticeti-Beluga consensus (paper Appendix D)

- Decision rules (direct, indirect; `Mysticeti/Consensus.lean`).
- Round-robin leader schedule, `leaderOf`.
- `ConsensusView`, `TransactionOrder` abstractions.

### 6.1 Safety

- L10 (round-robin pigeonhole), L13 (cert persistence), L14
  (no-skip), L15 (unique certified — proved by hand as a
  specialization of `certified_unique`), L16 (consistent decision
  status), Theorem 7 (consensus safety).
- `Mysticeti/Safety.lean`.

### 6.2 Liveness

- L8, L9, L11, L12, Theorem 6 (consensus liveness).
- Timing-flavored. `Mysticeti/Liveness.lean`.

## 7. Performance (paper Appendix C)

Deterministic worst-case bounds (L3, L4, L5).
`Beluga/PerformanceLemmas.lean`.

Probabilistic bounds (L6, L7, T5) are explicitly out of scope —
require a probability framework not adopted here.

## 8. Methodology: hand vs delegation

- The *math tactical wall* concept (with worked example: Lemma 10).
- Our delegation policy: file-disjoint frozen-files rule, attempt
  budget table, narrow-scope prompts.
- Concurrency: 7 Aristotle projects ran in parallel during the final
  proof push. Wall-clock improved by ~5–7x over sequential.
- The *content gap* counter-example
  (`NoEquivocationInParents` strengthening — wasn't a tactical wall;
  was a math content gap that Aristotle would have hidden).

Discussion: why this division works for us. When it might not.

## 9. Aristotle attribution table

(Take from [`docs/aristotle-attributions.md`](aristotle-attributions.md).)

Per-project: project ID, target file(s), theorems proved, helper
lemmas added, integration commit. Plus aggregate stats: total proofs
delegated, total hand-proved, ratio.

## 10. Reproducibility

- `lake update && lake build` gets a clean build with all proofs
  filled.
- `lake exe blocksynchroniser` runs the executable demo.
- All Aristotle prompts and project IDs are recorded in
  `docs/aristotle-projects.md` and
  `docs/aristotle-attributions.md`.

## 11. Limitations and future work

- **Probabilistic content** (App C L6, L7, T5): out of scope.
- **Per-validator network views**: our `SystemState` exposes a global
  operation log; full message-delivery semantics would let liveness
  proofs depend on actual delivery rather than abstracted timing.
- **Random pull complexity** (`O(1)` per validator): probabilistic.
- **Mysticeti-Beluga full consensus state**: our `ConsensusView` /
  `TransactionOrder` abstractions are parameters to Mysticeti theorems,
  not fields of `BelugaState`; integrating them into the executable
  protocol is future work.
- **Veil-style model checking** (deferred): could complement layer
  (D) of validation.

## 12. Conclusion

(One paragraph; written when all proofs land.)

## Appendices

- **A. File index** (matches [`formalization.md` § Repository layout](../formalization.md))
- **B. Sorry inventory** (final state — hopefully zero or near-zero)
- **C. Aristotle prompts archive**
- **D. Build trajectory** (sorry count over commits — see
  [changelogs/](../changelogs/))

## Status

Draft outline. To be filled in as proofs land. Sections most likely to
need revision:
- §5, §6.1, §6.2, §7 — proofs in flight, may surface unexpected
  subtleties.
- §8 — wait for round-3 outcomes to confirm parallelism numbers and
  wall/gap ratio.
