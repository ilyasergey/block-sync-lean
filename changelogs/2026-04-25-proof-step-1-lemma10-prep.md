# 2026-04-25 — Proof step 1: Lemma 10 statement preparation

First step of the proof-effort plan. Lemma 10 is the "simplest available"
slot but turns out to need Mathlib pigeonhole (`Finset.sum_le_card_nsmul`
/ `exists_lt_of_sum_lt`) — too much for a single small commit at hand.

Outcome: refined the statement (added the standard BFT hypotheses
`n = 3f + 1` and `honest count = 2f + 1`) and replaced the docstring
sketch with a fuller paper-tracked argument. Proof itself remains
`sorry`, **queued for Aristotle round 2**.

## What changed

- `BlockSynchroniser/Mysticeti/Safety.lean :: lemma10_round_robin_pigeonhole`:
  - Added hypothesis `hN : system.n = 3 * system.f + 1` (paper's
    standard minimum-honest-majority setup).
  - Added hypothesis `hHonest : (system.validators.filter (·.2)).length
    = 2 * system.f + 1` (consequence of `hN` + the `honestMajority`
    bound; making it explicit avoids re-deriving it inside the proof).
  - Refined the `PROVIDED SOLUTION` docstring with the explicit
    pigeonhole arithmetic: `6f + 3` honest contributions over `3f + 1`
    groups gives average > 2, so some group has ≥ 3.
- `docs/aristotle-projects.md`: added `lemma10_round_robin_pigeonhole`
  to the **Queued** list with the specific Mathlib lemmas the proof will
  rely on.

## Why not hand-prove

Hand-prove options considered:

- Direct construction by case analysis on Byzantine positions: `f` cases
  for "where the Byzantines fall in the 3f+3 window" — combinatorially
  large, doesn't scale uniformly in `f`.
- Sliding-window pigeonhole over groups: clean argument on paper but the
  Lean form requires `Finset.sum_le_card_nsmul` plus a counting argument
  for "each honest validator participates in 3 groups," which itself is
  non-trivial (involves `Nat.div_add_mod` reasoning over the round-robin
  schedule).

Conservative estimate for hand-prove: 100–150 LOC of Mathlib finesse.
Aristotle delegation is the better budget split per the policy in
[`docs/aristotle-workflow.md`](../docs/aristotle-workflow.md) — exactly
the case where "tactical wall on Mathlib lemmas → switch to Aristotle"
applies.

## Build

`lake build` clean (54 jobs, sorries unchanged at 25).

## Status delta

| Item | Before | After |
|---|---|---|
| `lemma10_round_robin_pigeonhole` | ◐ stated, vague hypothesis | ◐ stated with `n = 3f+1`, sketch tightened, queued for Aristotle |

## Next stage

Per the proof-effort plan (in this stage's parent narrative), step 2 is
`quorumIntersection`. Same pattern: prepare statement (already has the
right shape), confirm Mathlib path, queue for Aristotle. Or attempt
hand-proof first.

Stopping for next command.
