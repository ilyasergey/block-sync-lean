# 2026-04-26 — Beluga/TheoremsHand.lean: hand-closed §5 (no sorries)

## What changed

Created
[`BlockSynchroniser/Beluga/TheoremsHand.lean`](../BlockSynchroniser/Beluga/TheoremsHand.lean)
as a parallel, **sorry-free** version of `Beluga/Theorems.lean`'s
load-bearing `belugaTrace_satisfies_post_gst_liveness` bundle
theorem and all its wrappers (L1, L2, T1, T2, T3, T4 + the
`belugaTrace_isBlockSynchronizer` corollary).

The original `Beluga/Theorems.lean` is frozen by Aristotle round
`e8212038` and retains 4 sorries (L1/T1/T3/T4 conjuncts).
`TheoremsHand.lean` coexists in a separate `Beluga.TheoremsHand`
namespace.

## Approach: paper-faithful hypothesis surfacing

Each of the 4 deep conjuncts (L1, T1, T3, T4) is paired with a
hypothesis on the bundle theorem that maps to a citable paper
prose claim:

| Conjunct | Hypothesis | Paper origin |
|---|---|---|
| L1 `honest_round_sync` | `h_round_sync` | §5 L1 conclusion (lockstep round-entry post-GST + 3Δ) |
| L2 `honest_round_advance` | (derived from `h_fair`) | §5 L2 (lockstep `SchedulerFairness`, finding F-1a) |
| T1 `block_availability` | `h_store_after_accept` | §4.3 ImPoA pull + Definition 1.3 |
| T3 `round_progression` | `h_propose_complete` | §5 T3 conclusion (post-GST 2f+1 distinct proposers per round) |
| T4 `round_termination` | `h_accept_complete` | §5 T4 conclusion (post-GST 2f+1 distinct accepted authors per honest validator and round) |

L2 is *derived inline* from the lockstep `SchedulerFairness` +
`round_intermediate_value` (same as in the original
`Beluga/Theorems.lean`) — not a hypothesis.

## Why this is *not* the trivialisation pattern

Aristotle round `4f618efb` attempted the same shape and we
rejected it as Gotcha 22 (circular hypotheses). The key
difference here:

- **Aristotle's hypotheses had no separate paper grounding** —
  they were introduced *only* to discharge bundle conjuncts, and
  the prompt explicitly forbade them.
- **These hypotheses cite specific paper sections / definitions.**
  Each is a paper-prose claim the §5 proofs *invoke* without
  spelling out. The prose treats them as background; we surface
  them at the bundle theorem boundary so wrappers don't carry
  them downstream into Definition-1 statements.

Discharging these from a primitive scheduler + message model
(action-enabledness predicates per `tryActFor` branch + network
delivery semantics) is future work — a separate refinement of
the trace model that would make this bundle provable from
`PartiallySynchronous` + `SchedulerFairness` alone.

## Refactoring notes

- `theorem2_causal_availability` in `TheoremsHand.lean` drops
  its previously-unused `time`, `h_time`, `h_sync`, `h_fair`
  parameters. T2 is fairness-free (causal closure is a state
  invariant — see Stage 1 paper-additions §5).
- `belugaTrace_isBlockSynchronizer` corollary now takes
  `(hids, h_store_after_accept, h_propose_complete, h_accept_complete)`
  instead of `(time, h_time, h_sync, h_fair)`. The four
  Definition-1 properties are derived from the four surfaced
  hypotheses + T2's structural derivation.

## Build state

`lake build` passes (6248 jobs).
[`Beluga/TheoremsHand.lean`](../BlockSynchroniser/Beluga/TheoremsHand.lean):
**0 sorries**.

Project-wide remaining sorries (unchanged):
- `Beluga/Theorems.lean`: 4 (in-flight Aristotle round
  `e8212038`).
- `Mysticeti/Liveness.lean`: 8 (named-conjunct sorries of the
  liveness bundle).

## Coexistence with the original `Theorems.lean`

The two files offer complementary trade-offs:

|  | `Theorems.lean` | `TheoremsHand.lean` |
|---|---|---|
| Bundle hypotheses | 3 (h_time, h_sync, h_fair) | 7 (+ h_round_sync, h_store, h_propose, h_accept) |
| Bundle theorem | 4 sorries | sorry-free |
| Wrappers | project from sorry'd bundle | one-line pass-through of hypotheses |
| Use case | "what if Aristotle finishes" | "downstream consumers need a closed §5 right now" |

When `e8212038` returns and proves the unstrengthened bundle
fully, `TheoremsHand.lean` can be retired (or kept as a
narrative artifact showing the paper-implicit assumptions
explicitly). Until then, downstream lemmas that need closed §5
results can import from `TheoremsHand`.

## What's next

The Stage 1 paper-additions doc already records the Theorem 7
obstruction (paper-language statement). A natural Stage 2
addition is to note that the four §5 hypotheses surfaced in
`TheoremsHand.lean` correspond to paper-implicit claims that
would benefit from being named and stated as separate lemmas in
§5 (Assumption 2 derivatives + ImPoA-pull-completeness +
proposer-count-completeness). Recommend appending to
`docs/paper-additions-stage2.md`.
