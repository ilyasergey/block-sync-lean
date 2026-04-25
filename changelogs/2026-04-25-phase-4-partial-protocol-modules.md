# 2026-04-25 — Phase 4 partial: protocol modules (4a–4d)

Add the four building-block modules for Beluga's protocol semantics
(paper §4.2–§4.3). Held back from a single Phase-4 commit because the
phase is large; sub-phases land independently. Sub-phase 4e (HonestStep
+ executable `step` + refinement lemma) is the headline still-to-come
piece.

Concurrent with Aristotle project
`be7c0245-cdb9-4cce-9c4a-fffecfd1a69c` (filling the four `golden_*`
theorems in `Validation.lean`, which is frozen on this side). First
exercise of the **concurrency rule** from
[`docs/aristotle-workflow.md`](../docs/aristotle-workflow.md).

## Sub-phase 4a — BelugaState data types (commit `cbe907b`)

`BlockSynchroniser/Beluga/State.lean`.

- **`ReputationTable`** as an association list `List (ValidatorId × Nat)`
  (assoc list adequate for finite `n`; avoids `Finmap`/`HashMap` import
  for now). Operations: `lookup` (defaulting to `0`), `set`, `incr`,
  `decrBy` (saturating at 0 via `Nat`-truncated subtraction), `init`.
- **`BelugaValidator`** extends the abstract `Validator` (accepted /
  stored block digests) with the Beluga-specific fields from paper
  §4.2–§4.3: `reputation : ReputationTable`, `currentRound : Round`,
  `pendingBlocks : List BlockDigest`, `liveBulk : List BlockDigest ×
  List BlockDigest` (the live/bulk partition driving hybrid pull).
- **`BelugaValidator.toValidator`** — projection used by the
  `SystemState` typeclass instance (drops Beluga fields).
- **`BelugaState`** carries per-validator local state, the global block
  pool, and the operation log. The `SystemState BelugaState` instance
  *erases* the Beluga-specific fields, so all theorems stated against
  the abstract `SystemState` typeclass apply uniformly to Beluga states.
- **`BelugaState.init`**, **`BelugaState.getValidator`**.

Design note: kept the abstract `SystemState` typeclass and `Validator`
type unchanged; introduced Beluga-specific extensions as a separate
record + instance. This means the four Definition-1 properties in
`Properties.lean` apply unchanged to `BelugaState`.

## Sub-phase 4b — Reputation update rules (commit `cbe907b`)

`BlockSynchroniser/Beluga/Reputation.lean`. Implements paper §4.2 and
the corresponding pseudocode in Figure 8 (Appendix E, lines 23–32).

- **`reputationIncreaseCandidates`** (paper §4.2 increase rule;
  Figure 8 lines 24–29). `v_j` is a candidate iff at least `2f+1` of
  the input round-`r` blocks carry `watermark[j] = r-1`.
- **`updateScoreWithWatermarks`** (Figure 8 lines 23–30). Apply +1 to
  every candidate.
- **`reputationPenalty`** (paper §4.2 decrease rule; Figure 8 lines
  31–32). Subtract `R_L` (saturating at 0).
- **`reputationThreshold`** = `R_{2f+1} - R_L` per paper §4.2. Sort
  scores descending via `Array.qsort` with `decide (a > b)` Bool
  comparator; take the `(2f+1)`-th element.
- **`aboveThreshold`** — round-advancement rule (i) helper.

Design note: chose the paper text's framing (`watermark[j] = r-1` for
the candidate condition) over the slightly different Figure 8 phrasing
(`watermark[j] = r-2`); the discrepancy is an off-by-one in pseudocode
timing, not semantics. Documented inline.

## Sub-phase 4c — AdmissionControl (commit `dfa9b67`)

`BlockSynchroniser/Beluga/AdmissionControl.lean`. Implements paper §4.2
parent-selection and round-advancement rules; Figure 8 lines 14–17.

- **`isAcceptable`** / **`isAcceptableB`** — strict §4.2 version: `v_i`
  has output `block_accept` for `B`. The broader §4.3.1 version (also
  accepts implicitly-available blocks) lives in `Pull.lean` as
  `isAcceptableImPoA`.
- **`filterAcceptable`** — round-`(r-1)` candidates that `vid` has
  accepted.
- **`topByReputation`** — top `2f+1` ranked by author reputation
  (descending). Same `Array.qsort` machinery as `reputationThreshold`.
- **`acParentSelection`** (Figure 8 lines 14–17): filter then top-k.
- **`canAdvanceByQuorum`** — round-advancement rule (i): ≥ `2f+1`
  acceptable round-`r` blocks whose authors are above the threshold.

Forced detour: the original `isAcceptableB` used
`decide (HasAccepted ...)` but Lean's typeclass synth couldn't unfold
`HasAccepted` to find a `Decidable` instance. Fix landed in
`Trace.lean` (added explicit `Decidable` instances for `Emitted`,
`HasAccepted`, `HasStored`, `HasProposed`).

This `Trace.lean` edit triggered a transitive recompile of
`Validation.lean` (the file frozen for Aristotle), but did not touch
its source. Per the concurrency rule, source-level freezes hold across
transitive rebuilds.

## Sub-phase 4d — ImPoA / Hybrid pull (commit `3a2d934`)

`BlockSynchroniser/Beluga/Pull.lean`. Implements paper §4.3.

- **`implicitlyAvailable`** / **`…B`** (paper §4.3.1): `B` is
  implicitly available iff at least `f+1` distinct authors have
  blocks in subsequent rounds (`B'.r > B.r`) referencing `B` as a
  parent. Strong-link only for now (the paper allows weak-link
  inclusion too — same `f+1` threshold via at-least-one-honest
  reasoning).
- **`isLive`** / **`isLiveB`** / **`isBulk`** (paper §4.3.2). Live
  blocks are recent enough to affect quorum advancement in the
  current round; bulk blocks are stale. The paper's exact criterion
  depends on parent-availability state; we approximate with `B.r ≥
  currentRound - 1`. Refinement TBD.
- **`classifyMissing`** — partition missing digests into live/bulk.
  Drives the hybrid pull strategy in Figure 3(c).
- **`isAcceptableImPoA`** — broader §4.3.1 acceptability:
  `HasAccepted ∨ implicitlyAvailable`.

Out of scope (probabilistic, documented as deferred):
- Random pull complexity bound (`O(1)` per validator).
- Bulk module's randomized rotating pull strategy.

## What's deliberately *not* in this commit

- **`HonestStep`** relational small-step. Sub-phase 4e.
- **`step`** executable transition function. Sub-phase 4e.
- **Refinement lemma** (every `step` produces a transition satisfying
  `HonestStep`). Sub-phase 4e.
- **Driver `Main.lean` change** to actually run the executable step.
  Sub-phase 4e.

These four are the substantive part of Phase 4 — the data layer is
done; the dynamics layer is next.

## Build

`lake build` clean — 38 jobs. Sorries unchanged from Phase 3 baseline:

- `Quorum.lean :: quorumIntersection` (Phase 1, queued for Aristotle round 2)
- `Validation.lean ::` four `golden_*` (Phase 2, **in flight** with
  project `be7c0245-cdb9-4cce-9c4a-fffecfd1a69c`)
- `Patterns.lean :: certified_unique` (Phase 3, queued for Aristotle round 2)

## Aristotle work this stage

In flight, no integration yet:

| Project | Status | Files | Theorems |
|---|---|---|---|
| `be7c0245-cdb9-4cce-9c4a-fffecfd1a69c` | 🟡 IN_PROGRESS (~2%, 20+ min) | `Validation.lean` | 4 × `golden_*` |

See [`docs/aristotle-projects.md`](../docs/aristotle-projects.md).

## Status delta

Phase 4 sub-phases shifted six items from ☐ to ✅ in
[docs/formalization-status.md](../docs/formalization-status.md), now
updated to reflect 4a–4d landed structurally.

## Next stage

Sub-phase 4e: HonestStep relation, executable step function, refinement
lemma. Tentatively another ~600 LOC across one new file
(`Beluga/Protocol.lean`) plus `Main.lean` updates.
