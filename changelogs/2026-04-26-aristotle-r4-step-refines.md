# 2026-04-26 — Aristotle round 4: `step_refines_HonestStep`

## What changed

Integrated Aristotle project `a8889396-b34e-40f2-b10b-388f960c088e`
(round 4, returned ~02:20 SGT, status `COMPLETE_WITH_ERRORS`).

`step_refines_HonestStep` in
[`BlockSynchroniser/Beluga/Protocol.lean`](../BlockSynchroniser/Beluga/Protocol.lean)
is now proved at the top level. The proof is decomposed into seven new
private helpers:

| Helper | Status |
|---|---|
| `honestStep_of_no_op` | sorry-free |
| `honestStep_of_advance` | sorry-free |
| `honestStep_of_propose` | sorry-free |
| `honestStep_of_accept` | sorry-free |
| `honestStep_of_store` | sorry-free (delegates to `causal_history_of_find_none`) |
| `causal_history_of_find_none` | **sorry** — trace-level invariant deferred |
| `tryActFor_honestStep` | sorry-free |

## Why the remaining sorry

`causal_history_of_find_none` says: when `parentsAccepted` checks
have ensured no unaccepted block has all parents accepted (the accept
`find?` returns `none`) and `B` itself is accepted, then every block
reachable from `B` via `Reaches` is also accepted.

This is a trace-level invariant. At each accept step, `parentsAccepted`
is checked, so ancestors get accepted bottom-up — but proving this
requires reasoning about the cumulative state of the trace, not the
single-step state available to `step_refines_HonestStep`. It belongs
in a dedicated trace-invariant module (which we haven't built yet).

## Build state

- `lake build` passes (6244 jobs).
- Sorry count unchanged at 20 — `step_refines_HonestStep`'s sorry
  was replaced with a sorry'd helper, net 0.
- File status:
  - `step_refines_HonestStep` itself: ✅ at top level, transitively
    depends on the new helper sorry.

## Aristotle attributions

- Project `a8889396` (round 4) — see
  [`docs/aristotle-attributions.md`](../docs/aristotle-attributions.md)
  for full detail.

## What's next

- Wait for round 5 (`d32908b4`, Mysticeti/Liveness 11 helpers) and
  round 3a-followup (`58873be7`, Beluga/Theorems L1-L2-T1-T4).
- Eventually: build a trace-invariant module to discharge
  `causal_history_of_find_none` and unstick the §4 protocol-semantics
  status.
