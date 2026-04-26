# 2026-04-26 — Phase E foundations: clock-tracking + currentTime preservation

Per [`docs/plan-derive-fairness-from-primitives.md`](../docs/plan-derive-fairness-from-primitives.md),
this commit lands the Phase E *foundation lemmas* — the structural
facts about `networkTrace` that don't depend on scheduler-fairness
reasoning. The headline theorem `schedulerFairness_holds` is queued
for the next session (see "What's left" below).

## What changed

New file
[`Beluga/Network/Fairness.lean`](../BlockSynchroniser/Beluga/Network/Fairness.lean):

### Definitions

- **`NetworkDelivery`** (paper §2 primitive): post-GST,
  honest-honest push deliveries arrive within `Δ`. Stated against
  `networkTrace`'s `inboxes`.
- **`RoundEntryTimeBounded`**: `bv.roundEntryTime ≤ s.currentTime`
  at every state (structural invariant).
- **`CurrentTimeTracksTime`**: `(networkTrace system time k).currentTime
  = time k`.
- **`TimeoutFiresPast4Delta`**: at every post-`(roundEntryTime + 4Δ)`
  step, the timeout branch is enabled.

### Theorems (proved, no sorries)

- **`NetworkState.deliverPending_preserves_currentTime`**: the
  delivery operation only touches `inboxes` and `inflight`.
- **`networkTryActFor_preserves_currentTime`**: each of the four
  branches (propose, accept, store, advance) inherits
  `currentTime` from the input state via structure-update syntax.
- **`networkStep_currentTime`**: `(networkStep system s newTime).currentTime
  = newTime`. Combines the above.
- **`currentTime_tracks_time`**: by induction on `k`, the trace's
  `currentTime` equals `time k` at every step. (`CurrentTimeTracksTime`
  is now a derived theorem, not just a definition.)

These are the load-bearing structural facts for the rest of Phase E.
With `currentTime_tracks_time` in hand, every `time k`-comparison in
SchedulerFairness reduces to a `currentTime`-comparison on the
trace state, which the timeout branch's predicate consumes directly.

## Build state

`lake build` clean. **Beluga/Theorems.lean: 0 sorries** (unchanged).
`Beluga/Network/Fairness.lean: 0 sorries`. The headline theorem
`schedulerFairness_holds` is *not yet stated* — it will be added
when its proof is ready (no placeholder sorry).

## What's left for the full delivery

The plan's Phase E.4 (proving the headline theorem) and Phase F
(migrating Theorems.lean) require:

1. **Round-entry monotonicity invariant** (structural, ~80 lines).
   Prove `RoundEntryTimeBounded` as a theorem by induction on the
   trace, case-analyzing `networkTryActFor`'s four branches. Only
   the round-advance branch modifies `roundEntryTime` (sets it to
   `s.currentTime`); other branches preserve it; combined with
   `currentTime_tracks_time`, the invariant follows.

2. **`ActionScheduling` axiom** (definition).
   Add a second axiom alongside `NetworkDelivery`: post-GST, an
   honest validator with an enabled action is selected by the
   trace's scheduler (via `findSome?`) within `Δ` wall-clock. This
   captures paper §4.2's implicit "honest validators run the
   protocol" — finding F-1's missing primitive, surfaced.

3. **`schedulerFairness_holds`** theorem (medium, ~200 lines).
   From `NetworkDelivery` + `ActionScheduling` + the timeout
   branch + the foundation lemmas, derive that post-GST every
   honest validator advances within `4Δ + Δ = 5Δ` post-roundEntry.
   The bound becomes `5Δ` rather than the paper's nominal `3Δ`
   because we route through the timeout branch (the safety-net
   bound) rather than the optimistic 2f+1-quorum branch. The
   tighter `3Δ` bound requires modeling ImPoA pull dynamics in
   detail and is a refinement.

4. **Phase F migration** (Theorems.lean, ~50 lines).
   Replace the `SchedulerFairness` parameter in the §5 wrappers
   with `NetworkDelivery + ActionScheduling`. The `5Δ` bound
   propagates to L1, L2, and the bundle definition's
   `time k' ≤ time k₀ + 5 * system.Δ` clause.

Estimated remaining effort: 2–3 sessions of focused work, ~500–700
lines of Lean total.

## Architecture: why two axioms instead of one

The current `SchedulerFairness` axiom bundles:
- "Round progress happens" (liveness).
- "All honest catch up" (lockstep).
- "Within `3Δ`" (time bound).

This is the *conclusion* of paper L1 promoted to an axiom.

The post-Phase E factoring breaks it into two paper-faithful
primitives:
- **`NetworkDelivery`**: paper §2's `Δ`-bounded delivery.
- **`ActionScheduling`**: paper §4.2's implicit "honest validators
  run the protocol" — finding F-1 made explicit.

Both are at the level of the network/scheduler, not at the level
of round progress. Their combination (with the timeout branch)
*derives* round progress, rather than asserting it.
