# Formalization overview

Lean 4 formalization of [*Beluga: Block Synchronization for BFT Consensus
Protocols*](docs/Block_Sync_Project.pdf).

This file is the entry point. For deeper material, follow the pointers below.

## What we're building

Two deliverables, in priority order:

1. **The block synchronizer abstraction (paper §2.1, Definition 1).**
   The four properties any block synchronizer must satisfy:
   *Round-Progression*, *Round-Termination*, *Block availability*,
   *Causal availability*. These are the load-bearing definitions; the rest of
   the formalization either supports them, validates them, or proves the
   Beluga protocol satisfies them.

2. **Beluga the protocol (paper §4) and its main theorems (paper §5).**
   AC-based optimistic push (reputation, admission control) + ImPoA-based
   hybrid pull. Theorems 1–4 prove that an honest run of Beluga satisfies
   each property of Definition 1.

Stretch deliverable: the safety side of Mysticeti-Beluga (paper Appendix D —
Lemmas 10, 13, 14, 15, 16, Theorem 7). Out of scope: probabilistic content
(random pull complexity, Appendix C performance theorems), Mysticeti-Beluga
liveness (Theorem 6).

## Repository layout

```
block-sync-lean/
├── formalization.md             ← you are here
├── README.md                    ← build / run instructions
├── docs/
│   ├── Block_Sync_Project.pdf   ← the paper
│   ├── formalization-plan.md    ← phased plan with file layout
│   ├── formalization-status.md  ← per-item status, paper-to-Lean mapping
│   └── aristotle-workflow.md    ← when and how we delegate proofs
├── changelogs/                  ← timestamped entries per stage
├── BlockSynchroniser/
│   ├── Block.lean               ← Block, BlockDigest, ValidatorId, Round
│   ├── Validator.lean           ← per-node Validator state
│   ├── Operations.lean          ← block_propose / block_accept / block_store
│   ├── System.lean              ← BlockSynchroniserSystem (n, f, k, GST, Δ)
│   ├── State.lean               ← SystemState typeclass + DefaultSystemState
│   ├── Causal.lean              ← inductive Reaches; causal(B)
│   ├── Quorum.lean              ← IsQuorum; quorumIntersection (sorry)
│   ├── Trace.lean               ← Trace, traceInduction, Eventually, Has*
│   ├── Properties.lean          ← the four Definition-1 properties
│   ├── Validation.lean          ← non-vacuity sanity checks (golden_*, …)
│   └── Beluga/                  ← Phases 3–5: protocol + main theorems (TBD)
│       └── Mysticeti/           ← Phase 6 (stretch): safety bundle
├── Main.lean                    ← driver (Phase 4: runs the protocol)
├── lakefile.lean
└── lean-toolchain               ← v4.28.0
```

## Two kinds of theorems — do not confuse them

This is the most common source of confusion when reading the source. The
formalization deliberately separates them.

### Paper theorems

Statements that appear in the paper. They are *about Beluga the protocol*.

| Paper | Lean name (Phase 5) | What it claims |
|---|---|---|
| Theorem 3 (§5) | `theorem3_round_progression` | Beluga ⊨ Round-Progression |
| Theorem 4 (§5) | `theorem4_round_termination` | Beluga ⊨ Round-Termination |
| Theorem 1 (§5) | `theorem1_block_availability` | Beluga ⊨ Block availability |
| Theorem 2 (§5) | `theorem2_causal_availability` | Beluga ⊨ Causal availability |
| Lemma 1 (§5) | `lemma1_honest_round_entry` | After GST, all honest validators reach the same round within 3Δ |
| Lemma 2 (§5) | `lemma2_round_latency` | After GST, round-to-round latency ≤ 3Δ in the happy case |

These will live in [BlockSynchroniser/Beluga/Theorems.lean](BlockSynchroniser/) and
are stated against the Beluga-induced trace, not against any concrete
hand-built example. Status: planned (Phase 5).

### Validation lemmas (the `golden_*`, `realizable_*`, `not_*_emptyTrace`)

Statements in [BlockSynchroniser/Validation.lean](BlockSynchroniser/Validation.lean)
that **do not appear in the paper**. They are sanity checks on our *formalization*:

* `golden_roundProgression`, `golden_roundTermination`,
  `golden_blockAvailability`, `golden_causalAvailability` — claim that a
  concrete hand-built trace `goldenTrace` satisfies each property of
  Definition 1. If a `golden_*` proof won't go through, our formal version
  of the property is probably wrong — *and we want to find that out before
  attempting the corresponding paper theorem.*

* `realizable_propose`, `realizable_accept`, `realizable_store` — for each
  Definition-1 property of the form `P → ∃ Q`, the antecedent `P` is reachable
  in *some* trace. Rules out the failure mode where `P` is unsatisfiable and
  the property is therefore vacuously true.

* `not_roundProgression_emptyTrace`, `not_roundTermination_emptyTrace` — the
  empty trace fails at least one property. Rules out the failure mode where
  the property is so weak that even a no-op trace satisfies it.

> **Rule of thumb when reading the source.** Any theorem name starting with
> `golden_`, `realizable_`, or `not_*_emptyTrace` is *validation, not a paper
> result*. Theorem names starting with `theorem<N>_` or `lemma<N>_` correspond
> to paper Theorems N or Lemmas N respectively.

## Validation strategy (non-vacuity)

Every property in Definition 1 has the shape `P → ∃ Q` and is satisfied
vacuously by the empty trace. Three layers of defense:

| Layer | What it does | Example |
|---|---|---|
| **(A)** | Witness trace satisfying *all four* properties non-trivially | `goldenTrace ⊨ BlockSynchronizer system` |
| **(B)** | Antecedents are reachable somewhere | `realizable_propose : ∃ trace k vid B r, HasProposed (trace k) vid B r` |
| **(C)** | Empty trace fails at least one property | `¬ RoundProgression goldenSystem emptyTrace` |

(B) + (C) are mandatory and currently proved without `sorry`. (A) is stated
with `sorry` + `PROVIDED SOLUTION` sketches; we'll close them in sub-stage 2.5
(see [docs/formalization-plan.md](docs/formalization-plan.md)).

## How proofs get done

Hand-first, delegate-when-stuck. Aristotle (Harmonic's Lean prover) handles
proofs that are tedious or beyond easy hand-proving; we hand-prove definitions,
the four-property phrasings, validation scaffolding, and short tactical work.
Operational details — submission, diffing, attribution — are in
[docs/aristotle-workflow.md](docs/aristotle-workflow.md).

## Where to look

| Question | Doc |
|---|---|
| Per-item status, paper-to-Lean mapping | [docs/formalization-status.md](docs/formalization-status.md) |
| Phased plan, file layout, scope decisions | [docs/formalization-plan.md](docs/formalization-plan.md) |
| Aristotle delegation workflow | [docs/aristotle-workflow.md](docs/aristotle-workflow.md) |
| Per-stage changelog | [changelogs/](changelogs/) |
| The paper | [docs/Block_Sync_Project.pdf](docs/Block_Sync_Project.pdf) |

## Build

```bash
lake update
lake build
```

Lean toolchain pinned to `leanprover/lean4:v4.28.0` (matches Aristotle's
required version).
