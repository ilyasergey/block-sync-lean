# 2026-04-26 — Aristotle round 3e: PerformanceLemmas L3, L4, L5

## What changed

Integrated Aristotle project `91c97602-54da-4277-8bda-3864bfa6674a`
(submitted 2026-04-25 23:18 SGT, returned ~01:07 SGT, status
`COMPLETE_WITH_ERRORS`).

### Files

- **`BlockSynchroniser/Beluga/PerformanceLemmas.lean`** (modified):
  L3, L4, L5 (deterministic) proven sorry-free.
  - New definition `LatencyTriangle` capturing paper Assumption 1
    (latency triangle) at the trace-model level.
  - L4, L5 now take `h_lt : LatencyTriangle system time` as a
    hypothesis.
  - Private helper `round_advance_chain` proven by induction.
  - `import Mathlib` narrowed to `import Mathlib.Tactic`.
- **`BlockSynchroniser/Beluga/StepPreservation.lean`** (new):
  Aristotle introduced this module to host step-preservation lemmas
  needed for L3. Six lemmas, of which five compile sorry-free:
  - `updateValidator_getValidator_reputation` (sorry-free)
  - `tryActFor_preserves_reputation` ⟶ `sorry`: Aristotle's proof
    has a `▸` cast mismatch + simp heartbeat timeout in the
    `doAccept` branch; queued for round 3e-followup
  - `step_getValidator_reputation` (sorry-free; depends on the
    sorry'd lemma above)
  - `belugaTrace_getValidator_reputation` (sorry-free)
  - `init_getValidator_honest` (sorry-free after replacing `exact?`
    with `exact Or.inr h_find` per linter Try-this hint)
  - `belugaTrace_getValidator_honest` (sorry-free after replacing
    `exact?` with `exact init_getValidator_honest system vid h`)
- **`BlockSynchroniser.lean`**: added `import BlockSynchroniser.Beluga.StepPreservation`.
- **`docs/aristotle-projects.md`**: moved 91c97602 from Active to
  Completed; updated frozen-files list (PerformanceLemmas no longer
  frozen); added round 3e-followup entry to the Queued section for
  the remaining `tryActFor_preserves_reputation` sorry.
- **`docs/aristotle-attributions.md`**: full attribution entry for
  project 91c97602.

## Why

Round 3e was the deterministic part of paper Appendix C.2 (Beluga
performance bounds: L3 reputation non-decrease for honest validators,
L4 round latency = Δ post-GST, L5 round latency ≤ 2Δ or some malicious
validator gets blamed). These three lemmas use timing primitives we
introduced in Phase 4.5 plus the reputation table and round counter
already in `BelugaState`.

Aristotle correctly identified that the existing executable `step`
function never modifies `reputation` (proposing/accepting/storing
operations only mutate the block lists), so L3's non-decrease claim
is trivially preserved. To formalize this, Aristotle introduced
`StepPreservation.lean` with six bridge lemmas. For L4 and L5, it
added `LatencyTriangle` as a hypothesis — this is the trace-model
shadow of paper Assumption 1, and the paper itself uses Assumption 1
to derive these lemmas, so the hypothesis is faithful.

## Build state

- `lake build` succeeds (6244 jobs).
- Sorry count: 27 lines flagged by grep, 14 of which are real sorries
  (vs comment mentions or unrelated text). The new sorry is
  `tryActFor_preserves_reputation` in `StepPreservation.lean`.
- L3, L4, L5 themselves are sorry-free; only the deepest tactical
  lemma in the helper chain remains.

## Aristotle attributions

- Project `91c97602-54da-4277-8bda-3864bfa6674a` (round 3e)
  - L3, L4, L5 in `PerformanceLemmas.lean` (sorry-free)
  - `LatencyTriangle` definition + `round_advance_chain` helper
  - 5 of 6 helpers in `StepPreservation.lean` (sorry-free)
  - 1 helper sorry'd; queued for followup

## What's next

- Wait for in-flight Aristotle rounds to complete:
  - R2 (`4cda6cb1`): Quorum + Patterns + Mysticeti/Safety
  - R3a (`d724efd2`): Beluga/Theorems L1, L2 (timing)
  - R3b (`af54716b`): Beluga/Theorems T3, T4
  - R4 (`a8889396`): Beluga/Protocol step_refines_HonestStep
  - R5 (`d32908b4`): Mysticeti/Liveness 11 helpers
  - R6 (`9d7e8e08`): Mysticeti/Safety 3 bridge sorries
- Submit round 3e-followup for `tryActFor_preserves_reputation`,
  hinting Aristotle to use `convert`/`refine` instead of `▸`.
