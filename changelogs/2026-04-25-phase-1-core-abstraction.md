# 2026-04-25 — Phase 1: Core abstraction split

Decomposed the monolithic `Definitions.lean` into per-concept modules, added
`GST`/`Δ` to the system, replaced the path-based causal definition with an
inductive reachability relation, and stated the four properties of Definition 1
verbatim alongside the paper text.

## What changed

### New modules under `BlockSynchroniser/`

| File | Contents |
|---|---|
| `Block.lean` | `ValidatorId`, `Round`, `BlockDigest`, `Transaction`, `Block` |
| `Validator.lean` | `Validator` (per-node accepted/stored digests) |
| `Operations.lean` | `ValidatorOperation` = propose · accept · store |
| `System.lean` | `BlockSynchroniserSystem` with new `GST`, `Δ` fields; `isHonest`/`isByzantine` |
| `State.lean` | `SystemState` typeclass, `DefaultSystemState`, getters |
| `Causal.lean` | `isParent`, inductive `Reaches`, `causal` (replaces path-based version) |
| `Quorum.lean` | `IsQuorum`, **`quorumIntersection`** (stated; proof `sorry`) |
| `Trace.lean` | `Trace`, `traceInduction`, `Eventually`, `Emitted`, `HasAccepted`/`Stored`/`Proposed`, `authorOfDigest` |
| `Properties.lean` | The four Definition-1 properties + `BlockSynchronizer` conjunction |

### Removed

- `BlockSynchroniser/Definitions.lean` (decomposed; content moved or replaced).

### Modified

- `BlockSynchroniser.lean` — root re-exports the per-concept modules.
- `Main.lean` — drop dangling `import BlockSynchroniser.Definitions`.
- `docs/formalization-status.md` — Definition-1 rows flipped to ✅; quorum row added.

## Property phrasings

Each of the four Definition-1 properties is now stated verbatim from the paper
in its docstring, and the Lean form uses clean combinators:

- `RoundProgression` and `RoundTermination` use a single `∃ k` and
  `eraseDups`-counted authors against `2 * system.f + 1`.
- `BlockAvailability` and `CausalAvailability` use the new
  `Eventually trace k _` combinator and `HasAccepted`/`HasStored` predicates.
- `BlockSynchronizer` is the conjunction.

## Reachability — replaced

The previous list-based `isValidPath` / `causal` is gone. The new
`Reaches state B B'` is an inductive `Prop` with constructors `refl` and
`step`, suitable for direct induction. `causal state B := Reaches state B`.

## Build

`lake build` clean — 24 jobs, single expected `sorry` warning on
`quorumIntersection`.

## Sorries introduced

- `BlockSynchroniser/Quorum.lean :: quorumIntersection` — pigeonhole-style
  cardinality argument. Plan: prove by hand using Mathlib's
  `Finset.card_inter_add_card_union`, or delegate to Aristotle if it bogs down.

## Aristotle work this stage

None. All Phase-1 changes were structural; no proofs were attempted.

## Next stage

Phase 2 — Validation lemmas. Construct `goldenTrace` (a concrete `n=4, f=1`
honest-synchronous trace), prove `goldenTrace ⊨ BlockSynchronizer system`
non-trivially, add the realizability lemmas, and the anti-witness traces
(`emptyTrace`, `byzantineOnlyTrace`).
