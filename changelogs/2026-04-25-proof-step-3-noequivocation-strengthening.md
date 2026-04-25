# 2026-04-25 — Proof step 3: NoEquivocationInParents strengthening + certified_unique prep

Step 3 of the proof-effort plan. Identified a *content gap* (not a
tactical wall) blocking `certified_unique`: the existing
`NoEquivocationInParents` only covers parents of *one* block; the
proof needs the cross-block version.

This is genuine math content that needs human attention, not
delegation. Fixed; lemma still sorry'd because its proof also depends
on `quorumIntersection` (queued).

## What changed

### `BlockSynchroniser/Beluga/Patterns.lean :: NoEquivocationInParents`

Strengthened from within-block to cross-block:

- **Before**: `∀ B parent₁ parent₂, B ∈ blocks → honest B.author → ...`
  — required the two parents to share *one* honest block.
- **After**: `∀ B₁ B₂ parent₁ parent₂, B₁ ∈ blocks → B₂ ∈ blocks →
  honest B₁.author → honest B₂.author → ...` — covers conflicting
  parent references across two distinct honest-authored blocks.

The within-block version is the specialization `B₁ = B₂`; nothing in
the formalization that previously used the predicate is broken (no
proofs through the predicate yet — it was a hypothesis to
`certified_unique` and `lemma13`/`lemma14` placeholders).

### `BlockSynchroniser/Beluga/Patterns.lean :: certified_unique`

Refined `PROVIDED SOLUTION` docstring with the now-precise proof
strategy:

1. `strongReferencerAuthors` of `B₁`, `B₂` are quorums (`> 2f` from cert
   pattern).
2. Apply `Quorum.quorumIntersection` to get `≥ f+1` shared. Pick an
   honest `h` in the shared list (counting Byzantines `≤ f`).
3. `h` participates in both author-lists, so there are blocks
   `C₁`, `C₂` (possibly distinct!) authored by `h` with `B₁.d`,
   `B₂.d` respectively as parents.
4. Apply `NoEquivocationInParents` (cross-block form) to
   `(C₁, C₂, B₁, B₂)` using same-author + same-round to conclude
   `B₁ = B₂`.

The cross-block form was the missing piece. The proof is straightforward
once `quorumIntersection` lands.

## Build

`lake build` clean (54 jobs, sorries unchanged at 25). The strengthened
predicate compiles cleanly because it was only used in `sorry`-bound
proofs.

## Status delta

| Item | Before | After |
|---|---|---|
| `NoEquivocationInParents` | within-block only | cross-block (stronger; correct precondition for `certified_unique`) |
| `certified_unique` | proof sketch was incomplete (didn't account for `C₁ ≠ C₂` case) | proof sketch now sound; queued |

## Reflection on the pattern

This step is a counterpoint to steps 1 and 2 (which were tactical
walls). Here the issue was a *content gap*: the math was wrong, not the
plumbing. Cues that distinguished:

- I tried to write the proof on paper and discovered a case I couldn't
  close (the `C₁ ≠ C₂` case).
- Aristotle would have produced the same `sorry` (or worse, an
  invalid proof relying on the under-specified hypothesis).

The decision-cue table in
[docs/math-tactical-wall.md](../docs/math-tactical-wall.md) calls this
out: "Are you sure the statement is correct?" — if no, don't delegate
yet. Strengthen the statement first.

## Next stage

Two natural directions:

- **Step 4: Aristotle round 2** — submit `quorumIntersection`,
  `certified_unique`, and `lemma10_round_robin_pigeonhole` together.
  All three are independent tactical walls, all prep'd.
- **Step 4 (alt): hand-prove `step_refines_HonestStep`** — case
  analysis on the executable `step`'s `findSome?` result, no Mathlib
  needed. Real concrete proof; ~80–150 LOC.

Stopping for next command.
