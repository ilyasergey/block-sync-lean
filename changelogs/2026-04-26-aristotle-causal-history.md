# 2026-04-26 — Aristotle round 4-followup: `causal_history_of_find_none` via three-stage trace invariant

## What changed

Integrated Aristotle project `3f6cf619-5a7f-4142-9114-c46caafa025f`
(round 4-followup, returned ~11:10 SGT, status **`COMPLETE`** —
fully clean).

`causal_history_of_find_none` in `Beluga/Protocol.lean` is now proved
sorry-free. As a consequence, `step_refines_HonestStep` is fully
closed transitively.

## How

The single-state form of the lemma was unprovable (the `find? = none`
hypothesis gives forward closure, but `Reaches` goes backward — type
mismatch). Aristotle restructured around a three-stage trace invariant:

1. **`BlockInv`** — every block has canonical digest, corresponding
   `block_propose` op in the log, uniqueness per (validator, round)
   pair, bounded author IDs. Implies no-duplicate-digests.
2. **`AcceptInv`** — accepted digest ⇒ all parent digests accepted +
   accepted digest ⇒ block in pool. Hardest case: `doAccept` (uses
   no-duplicate-digests so the parent check covers all blocks).
3. **`CausallyClosed`** — derived from `AcceptInv` by induction on
   `Reaches`: at each parent step the intermediate block is in the
   pool and accepted, so its parent digests are accepted by
   `acceptedParents`.

Plus `causallyClosed_trace`: `CausallyClosed` holds at every trace
step.

## Signature changes

To thread trace ancestry:

- `causal_history_of_find_none` now takes `system`, `hids : ValidIds system`,
  `hTrace : ∃ k, s = belugaTrace system k`.
- `honestStep_of_store`, `tryActFor_honestStep`, `step_refines_HonestStep`
  also take `hids` and `hTrace` (propagation only — no semantic change).

## Build state

- `lake build` succeeds (6246 jobs).
- `Beluga/Protocol.lean` is now **0 sorries** (was 1).
- Sorry delta: −1 across the project.

## Aristotle attributions

- Project `3f6cf619` — see
  [`docs/aristotle-attributions.md`](../docs/aristotle-attributions.md).

## Pattern recap

This round + the admission-invariant round are the two big trace-
invariant landings. Both used a *compound carrier* (3- or 4-property
hierarchy preserved across `tryActFor`). When the proof you're after
isn't a single-state fact but a trace property, give Aristotle:

- The shape of the invariant carrier (compound, with the dependent
  properties named).
- The induction structure on the trace.
- Time — these rounds run ~5–9 hours.

## What's next

- One round in flight: `e3bb7fb6` (theorems-mains, L1, L2, T1–T4
  under `SchedulerFairness`). At ~6% progress as of wakeup.
- After that: 14 protocol-invariant sub-sorries in
  Mysticeti/Liveness from r5; can be split into focused rounds
  along the F-1/F-5 categories.
- F-7 (T7 safety/liveness boundary) still open.
