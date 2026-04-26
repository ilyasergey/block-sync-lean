# 2026-04-26 — Aristotle 4f618efb (Beluga §5 bundle), selective integration

## What changed

Integrated Aristotle project `4f618efb-b2b3-4c61-bfb8-ebc339a949dc`
(post-gst-liveness round, returned ~16:30 SGT, status
**`COMPLETE_WITH_ERRORS`**) into `Beluga/Theorems.lean`.

The integration is **selective**: 5 sorry-free helper lemmas plus an
inline L2 derivation are kept; 4 conjuncts of the bundle theorem
that Aristotle "trivialised" by lifting them to hypotheses are
discarded and re-stubbed for the next round.

### Integrated (sorry-free)

5 trace-structure lemmas, all marked
`-- proof: aristotle (project 4f618efb) — beluga-§5-bundle round`:

1. `doAdvance_round_at_most_one` — `doAdvance` increments the target
   round by at most 1.
2. `step_round_at_most_one` — `step` increases any validator's
   `currentRound` by at most 1 (case analysis on `tryActFor`'s four
   branches; mirrors `step_round_monotone`, with `maxHeartbeats 800000`).
3. `honest_validator_persistent_trace` — honest validators are present
   at every trace step.
4. `round_monotone_trace` — round monotonicity across arbitrary
   `k₁ ≤ k₂`.
5. `round_intermediate_value` — **intermediate-value theorem for
   validator rounds**: if a validator's round is `≤ r` at `k₁` and
   `≥ r` at `k₂`, then there is a `k ∈ [k₁, k₂]` where the round is
   exactly `r`. The key piece needed for L2's "step at exactly
   `r + 1`" guarantee.

### Integrated (inline derivation)

The `honest_round_advance` (L2) conjunct of
`belugaTrace_satisfies_post_gst_liveness` is now derived inline
(not a sorry) using `round_intermediate_value` + the now-strengthened
lockstep `SchedulerFairness`.

### Discarded — Aristotle's trivialisation

Aristotle introduced 5 new theorem hypotheses to prove the bundle:
- `h_lockstep`: a strengthening of `SchedulerFairness` to `≥ r + 1`.
  **Useful** — absorbed into our redefined `SchedulerFairness`.
- `h_round_sync`: literally the L1 conclusion = the
  `honest_round_sync` field of the bundle. **Circular.**
- `h_store_liveness`: literally the T1 conclusion. **Circular.**
- `h_propose_complete`: literally the T3 conclusion. **Circular.**
- `h_accept_complete`: literally the T4 conclusion. **Circular.**

The bundle proof was then `refine ⟨h_round_sync, ?_,
h_store_liveness, h_propose_complete, h_accept_complete⟩` with only
the L2 case derived non-trivially from `h_lockstep`. The bundle
proof typechecks but the bundle is just the conjunction of its
hypotheses, so the theorem becomes vacuous when applied to any
context that doesn't already have those conjuncts in hand.

We discarded the 4 circular hypotheses and re-stubbed
`belugaTrace_satisfies_post_gst_liveness` with 4 sorries (L1, T1,
T3, T4) for the next round.

## Definition change — `SchedulerFairness` is now lockstep

`SchedulerFairness` was strengthened from "every honest validator
reaches round `≥ r` within `3Δ`" (catch-up) to "every honest
validator reaches round `≥ r + 1` within `3Δ`" (lockstep). This is
the variant actually needed to derive L2 (whose conclusion is "round
`r + 1` within `3Δ`"). The catch-up form gives the wrong target
round.

This is **F-1a** added to
[`docs/mechanization-findings.md`](../docs/mechanization-findings.md):
the round-level corollary of paper Assumption 2 must be stated in
lockstep form to support L2's prose argument.

## Pattern documented — Aristotle's "bundle trivialisation" failure mode

When stuck on the inductive carrier of a bundle theorem, Aristotle
can "close" each conjunct by adding a hypothesis equal to the
conjunct's conclusion. The proof typechecks but the result is
vacuous. Mitigations:

1. *Selectively integrate* — keep helper lemmas + non-circular
   conjuncts, discard circular hypotheses.
2. Resubmit with explicit anti-trivialisation language: "no
   hypothesis matching a conjunct's conclusion is acceptable; you
   may extend the bundle structure with extra carrier conjuncts as
   long as the bundle is provable inductively from `belugaTrace`
   without extra fairness assumptions beyond Assumption 2."

A sequel to Gotcha 21 ("Bundle inductive invariants before
delegating") in
[`docs/blog-aristotle-integration-gotchas.md`](../docs/blog-aristotle-integration-gotchas.md)
will be added once the resubmission round either succeeds or fails
(empirical evidence about whether the anti-trivialisation prompt
works).

## Build state

`lake build` passes (6248 jobs). Sorries remaining:
- `Beluga/Theorems.lean`: 1 (the bundle theorem with 4 internal
  sorries — re-counted as 1 by `grep`).
- `Mysticeti/Liveness.lean`: 1 (Mysticeti bundle, in flight as
  `03f5fe3f`).

## Aristotle attribution

- Project `4f618efb-b2b3-4c61-bfb8-ebc339a949dc` — full attribution
  appended to
  [`docs/aristotle-attributions.md`](../docs/aristotle-attributions.md).

## What's next

1. Resubmit `belugaTrace_satisfies_post_gst_liveness` as a new
   project with stricter prompt (no circular hypotheses; bundle
   structure may be extended with extra carrier conjuncts as long
   as inductively provable from `belugaTrace`).
2. Wait for `03f5fe3f` (Mysticeti bundle) — examine for the same
   trivialisation failure mode.
3. After bundle theorems land, return to the
   [`Mysticeti/Safety.lean`](../BlockSynchroniser/Mysticeti/Safety.lean)
   refactor: rely on `belugaTrace_admissionWellFormed` to eliminate
   `AdmissionWellFormed` hypotheses, identify additional Safety
   hypotheses (`h_view_traceback`, `h_decision_complete`,
   `h_authors_valid`, `h_byz_bound`, `h_honest_unique`, `h_no_eq`)
   that can be folded into trace invariants.
