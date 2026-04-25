# 2026-04-25 — Phase 3: Beluga block extensions and patterns

Add Beluga's extended block (paper §4.1) and the two block patterns
(paper §4.4). Stand up the load-bearing safety statement
`certified_unique` with a `PROVIDED SOLUTION` sketch.

This phase ran **concurrently with sub-stage 2.5** — Aristotle is
processing the four `golden_*` proofs in
[BlockSynchroniser/Validation.lean](../BlockSynchroniser/Validation.lean) on
a separate file path while this work proceeds in
[BlockSynchroniser/Beluga/](../BlockSynchroniser/Beluga/). First exercise of
the concurrency rule from
[docs/aristotle-workflow.md](../docs/aristotle-workflow.md).

## What's new

### `BlockSynchroniser/Beluga/BlockExt.lean`

- `BelugaBlock` extends `Block` with the three Beluga-specific fields
  (paper §4.1):
  - `weaklinks : List BlockDigest` — accepted but non-parent references
    (used by ImPoA pull mechanism).
  - `watermark : List Round` — `n`-element array; `watermark[i]` = highest
    round of any block received from `v_i` (used by AC reputation update).
  - `ancestors : List Round` — `n`-element array; `ancestors[i]` = highest
    round of `v_i`'s blocks reachable via strong links (used by live/bulk
    classification).
- `BelugaBlock.WellSized system B` — predicate that `watermark`/`ancestors`
  arrays match `system.n` length.

### `BlockSynchroniser/Beluga/Patterns.lean`

- `strongReferencerAuthors state B` — distinct authors of blocks in `state`
  that reference `B` as a parent.
- `availabilityPattern system state B` — `> f` distinct strong references
  (paper §4.4 availability pattern). Strong-link-only for now; the
  weaklinks-inclusive variant lands in Phase 4 alongside Beluga state.
- `certificatePattern system state B` — `> 2f` distinct strong references
  (paper §4.4 certificate pattern).
- `available`, `certified` — abbreviations.
- `NoEquivocationInParents system state` — predicate that honest validators
  never include two parents with the same `(author, round)`. Phase 4 will
  prove this for any state induced by Beluga's protocol semantics; stated
  abstractly here.
- **`certified_unique`** (paper §4.4 / Appendix D Lemma 15) — the
  load-bearing safety theorem: two certified blocks sharing author and
  round are equal. Stated with `NoEquivocationInParents` as a hypothesis.
  Proof is `sorry` with a `PROVIDED SOLUTION` sketch citing
  `Quorum.quorumIntersection`. **Queued for delegation to Aristotle in
  round 2.**

### Module integration

- `BlockSynchroniser.lean` re-exports the two new modules.

## Build

`lake build` clean — 30 jobs. Sorry warnings:

- `Quorum.lean :: quorumIntersection` (Phase 1)
- `Validation.lean ::` four `golden_*` (Phase 2; **currently being filled by
  Aristotle, project `be7c0245-cdb9-4cce-9c4a-fffecfd1a69c`**)
- `Patterns.lean :: certified_unique` (this stage; queued for Aristotle
  round 2)

## Aristotle work this stage

In flight (sub-stage 2.5, concurrent with this commit):

| Project | Status | Files |
|---|---|---|
| `be7c0245-cdb9-4cce-9c4a-fffecfd1a69c` | IN_PROGRESS | `Validation.lean`: 4 `golden_*` theorems |

Result will be integrated in a separate sub-stage commit so the diff is
isolated and the provenance attribution is unambiguous.

## Status delta

| Category | Before | After |
|---|---|---|
| §4 Beluga protocol | 0 done / 11 planned | 4 done / 2 in progress / 6 planned |
| Total ✅ | 14 | 18 |
| Total ◐ | 7 | 8 |
| Total ☐ | 23 | 18 |

## Next stage

Wait for Aristotle's result on the four `golden_*` theorems. When it
returns, run the operational recipe (extract → diff → review → apply →
verify → commit) per
[docs/aristotle-workflow.md](../docs/aristotle-workflow.md). Then pick:

- Continue with **Phase 4** (Beluga protocol semantics — reputation,
  AC, ImPoA, executable `step` + refinement).
- Or schedule **Aristotle round 2** for `certified_unique` and
  `quorumIntersection` if we want to clear those before Phase 4.
