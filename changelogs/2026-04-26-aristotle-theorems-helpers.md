# 2026-04-26 — Aristotle theorems-helpers round + scope-discipline lesson

## What changed

Integrated Aristotle project `b544affb-b9a9-4f8c-965f-2a31051ef75f`
(theorems-helpers round, returned ~10:25 SGT, status **`COMPLETE`** —
fully clean, no `_WITH_ERRORS`).

Both target helpers in `Beluga/Theorems.lean` are now sorry-free:

- `step_preserves_validator_ids` — `step` never removes a validator ID.
- `step_round_monotone` — `step` never decreases any validator's
  `currentRound`.

One new auxiliary `updateValidator_none` was added. Both targets use
`set_option maxHeartbeats 800000 in` scoped per-lemma for the deep
`tryActFor` case analysis.

## Scope-discipline lesson

This round *replaced* the canceled `58873be7` round, which had bundled
8 targets (L1, L2, T1–T4 + 2 helpers) under a single submission and
stalled at ~13% progress for over 7 hours. The tighter 2-target scope
completed in ~80 minutes with `COMPLETE` status (not even
`_WITH_ERRORS`).

**Lesson for the workflow:** for trace/inductive helpers — and
generally for any prompt asking for ≥4 substantive proofs in one
submission — the throughput is much better when scoped to ~2 targets
that share infrastructure. Bundling causes Aristotle to thrash on
the dependency graph. Recommend updating
`docs/aristotle-workflow.md` with this scope-discipline note in a
future pass.

## Next submission

`e3bb7fb6-40cd-4cd9-8f22-c8f8e6c621fc` — same file, the 6 main
theorems (L1, L2, T1–T4) under `SchedulerFairness`, now built on
the helpers that just landed.

## Build state

`lake build` succeeds (6246 jobs). Sorry delta: −2 (both helper
stubs closed).

## What's next

- Wait for `e3bb7fb6` (theorems-mains) and `3f6cf619` (causal_history,
  still in flight).
- After both: 14 protocol-invariant sub-sorries from r5 in
  Mysticeti/Liveness; can be split into ~4–5 focused rounds.
- F-7 (T7 safety/liveness boundary) still open.
