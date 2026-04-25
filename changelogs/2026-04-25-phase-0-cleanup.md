# 2026-04-25 — Phase 0: Cleanup

Mechanical cleanup before structural work begins.

## What changed

- **Deleted** `BlockSynchroniser/Existing/` (legacy ssreflect-using exploration code, not imported by the build target):
  - `DAGBasedCertified.lean`
  - `DAGBasedOPT.lean`
  - `Scratchpad.txt`
- **Removed from `BlockSynchroniser/Definitions.lean`**:
  - `blockSynchroniserValidity` — not part of Definition 1; stronger than the paper requires.
  - `blockSynchroniserCommonSet` + helpers (`allHonestValidatorsEventuallyStore`, `authorsInCommonSet`) — not part of Definition 1; derivable from Round-Termination + Block-availability.
- **Verified**: `state_kz` typo at line 228 is no longer present (already corrected upstream).

## Verification

`lake build` succeeds clean (8/8 jobs).

## Status delta

`Definitions.lean` now contains exactly the four Definition-1 properties (still under their old names: `blockSynchroniserProgressI/II`, `blockSynchroniserAvailability`, `blockSynchroniserCausalAvailability`). Renames to match the paper's terminology come in Phase 2.

## Next stage

Phase 1 — Core abstraction split. Break `Definitions.lean` into the per-concept files declared in the plan, add `GST`/`Δ`, replace `Path`/`isValidPath`/`causal` with an inductive `Reaches` predicate, and define `Quorum` + the quorum-intersection lemma.
