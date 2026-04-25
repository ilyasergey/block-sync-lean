# 2026-04-26 — Aristotle round 5: Mysticeti/Liveness 11 helpers

## What changed

Integrated Aristotle project `d32908b4-d387-4d77-ac37-87e03a6f6699`
(round 5, returned ~05:30 SGT, status `COMPLETE_WITH_ERRORS`).

The 11 sorry'd helper lemmas underpinning lemma8 / 9 / 11 / 12 / T6
(introduced in round 3d) now have *structured proofs* that follow the
paper's argument (§D.2). Compositional steps are spelled out;
protocol-invariant atomic facts are sorry'd as named inline sub-steps.

## Newly proved auxiliaries (sorry-free)

- `mem_of_mem_eraseDups`
- `belugaTrace_blocks_monotone` (blocks added to state are never removed)

## Caller fixup

`three_consecutive_honest_direct_commit` now threads the F-8 `h_ids`
hypothesis (validator IDs are 0..n-1) through to
`lemma10_round_robin_pigeonhole`. Aristotle's tarball pre-dated
round 2's signature change; fixed during integration.

## Sub-sorry breakdown

14 inline sorries remain inside the 11 helpers, each named after the
protocol invariant it depends on:

| Invariant | Count | Why deferred |
|---|---|---|
| Step / `doAdvance` / `doPropose` round timing | 6 | Trace-level invariant of `step` semantics |
| BFT bound (`n = 3f+1`, honest = 2f+1) | 2 | Standard BFT side conditions |
| Validator-IDs contiguous (F-8) | 1 | Same |
| Parent-selection invariant | 2 | Honest validators include available leader blocks |
| ImPoA / availability | 1 | Pull-protocol availability |
| TransactionOrder axioms | 1 | Abstract-parameter axioms |
| Backward-induction sub-step | 1 | Indirect-decision rule chain |

## Build state

`lake build` succeeds (6246 jobs). Sorry count rose by ~13 (each
helper's bare-sorry body became a real proof that bottoms out in
multiple named atomic invariants). This is a structural net win:
each new sorry is a clearly-named protocol invariant for a future
focused round, rather than an opaque body.

## Aristotle attributions

- Project `d32908b4` (round 5) — see
  [`docs/aristotle-attributions.md`](../docs/aristotle-attributions.md)
  for full detail.

## What's next

- Wait for in-flight rounds (3a-followup `58873be7`, 4-followup
  `3f6cf619`, admission-invariant `9f17cf80`).
- Eventually: a focused round (or multiple) on the 14 named atomic
  invariants. Most cluster under "step semantics" — they'd be a
  natural fit for a future trace-invariants module similar to
  `StepPreservation` and `AdmissionInvariant`.
