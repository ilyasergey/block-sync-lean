# 2026-04-25 — Proof step 2: quorumIntersection prep + math tactical wall doc

Step 2 of the proof-effort plan. Same pattern as step 1: Mathlib-heavy
cardinality argument hits the same wall as Lemma 10.

User reaction to step 1's "tactical wall" framing prompted writing
[docs/math-tactical-wall.md](../docs/math-tactical-wall.md) as a
prominent stand-alone document, intended as the seed for a future blog
post.

## What changed

### `BlockSynchroniser/Quorum.lean :: quorumIntersection`

- Added hypothesis `hN : system.n = 3 * system.f + 1`. Without it the
  statement is *false*: with `n = 3f+2` the standard `(2f+1) + (2f+1) - n`
  bound gives `f`, not `f+1`.
- Refined `PROVIDED SOLUTION` docstring with explicit Mathlib path:
  `Finset.card_inter_add_card_union`, `Finset.card_le_card`, then the
  arithmetic.

Queued for Aristotle round 2.

### New doc: `docs/math-tactical-wall.md`

A stand-alone working note defining the *math tactical wall* — the
moment when a proof's bottleneck shifts from mathematical reasoning to
Lean tactic plumbing. Sections:
- Definition.
- Why it matters for human/AI division of labor (asymmetry: AI has
  internal Mathlib search, humans don't).
- Worked example: Lemma 10's pigeonhole + counting.
- When to push through vs delegate (decision-cue table).
- How it shapes our workflow (calibrated attempt budget).
- Pitch for a future blog post.

### `docs/aristotle-workflow.md`

Added a "Concept: the math tactical wall" cross-reference section
pointing at the new document.

### `formalization.md`

Added a row in "Where to look" pointing at
[docs/math-tactical-wall.md](../docs/math-tactical-wall.md).

### `docs/aristotle-projects.md`

`quorumIntersection` was already in the queued list (with a brief note);
no edit needed.

## Build

`lake build` clean (54 jobs, sorries unchanged at 25).

## Status delta

| Item | Before | After |
|---|---|---|
| `quorumIntersection` | ◐ stated, no `n=3f+1` | ◐ stated with `n=3f+1`, sketch tightened, queued |

## Next stage

Step 3 of the plan: `certified_unique`. It depends on
`quorumIntersection` *for the proof*, but the **statement** doesn't
change. I plan to hand-attempt the proof using the (still-sorried)
`quorumIntersection` as a lemma. The proof will compile — the resulting
`certified_unique` will be "proved modulo `quorumIntersection`" — once
that lands, this lemma becomes fully proved automatically.

There's also a *content gap* (not a tactical wall): `NoEquivocationInParents`
as currently stated covers parents *within one block*; the proof of
`certified_unique` needs cross-block non-equivocation for the case where
the shared honest validator's referencing block for `B₁` is different
from the one for `B₂`. I'll need to strengthen the hypothesis (or
expose a separate one) before the proof goes through. That's a
substantive math change, not delegation territory.

Stopping for next command.
