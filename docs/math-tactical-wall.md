# The math tactical wall

A working note on a recurring pattern in this formalization: a single phrase
that's becoming load-bearing for our human/AI division of labor. Worth
expanding into a blog post.

## Definition

A *math tactical wall* is the moment in a formalization where the bottleneck
shifts from **mathematical reasoning** to **tactic plumbing**. The math is
clear; the work that remains is figuring out:

* which Mathlib lemma to invoke,
* what shape the goal needs to be in for that lemma to apply,
* how to massage the data structures (`List ↔ Finset`, `Prop ↔ Bool`,
  `≤ ↔ <`, etc.) so types line up,
* which `simp` set / `ring` variant / `omega` form discharges the
  arithmetic step.

It's not "I haven't worked out the math". It's: "I see the proof on paper;
I just can't find the Lean idiom."

## Why this matters for human/AI division of labor

When a human engineer hits a math tactical wall, they:

* burn time on trial-and-error (`simp [<some>]` / `exact?` / `apply?` /
  Mathlib search),
* learn nothing about the underlying mathematics (the math was already done
  before the wall),
* often give up and write `sorry` anyway.

When Aristotle (or a similar Lean-trained agent) hits the same wall, it:

* has internal Mathlib search and recognizes the lemma family,
* pattern-matches on goal shape and unification,
* often closes the goal in one step.

This asymmetry is the load-bearing argument for delegation. The strength
of the human/AI partnership isn't "AI can do math humans can't" — it's
"AI can plumb Lean idioms humans don't want to plumb." The math content
flows through the human (architecture, statements, sketch); the tactical
wall flows through the AI.

## A worked example: Lemma 10 (round-robin pigeonhole)

Paper `Beluga` Appendix D Lemma 10. The math, in two lines:

> In any window of `3f+3` rounds with `n = 3f+1` validators in a round-robin
> schedule, some triple of three consecutive rounds has all-honest leaders.
> Counting argument: `(6f+3)/(3f+1) > 2`, pigeonhole.

That's the entire mathematical content. Now the Lean side:

* Define `groupHonestCount : Fin (3f+1) → ℕ` via `Finset.range`/`Fin`/some
  appropriate finite type — does the existing `BlockSynchroniserSystem`
  already give us a `Fintype` instance, or do we synthesize one?
* Prove `Σ groupHonestCount = 3 · (2f+1) = 6f+3`. This needs each honest
  validator to participate in exactly 3 groups, which is itself a
  `Nat.div_add_mod`-flavored counting argument over the round-robin
  schedule.
* Apply pigeonhole. Mathlib has `Finset.exists_lt_of_sum_lt`,
  `Finset.sum_le_card_nsmul`, `Nat.exists_lt_of_sum_le` — which one fires?
  What's the exact goal shape it expects?
* Massage `> 2` into `≥ 3`. Trivial on paper; in Lean, choose between
  `Nat.lt_iff_add_one_le`, `Nat.succ_le_iff`, or `omega`.

A working Lean proof is probably 100–150 lines. Aristotle delegates this
in a couple of round-trips. A human iterating with `apply?` and
`exact?` is the wrong tool.

## When to push through anyway

Not every "I can't prove it yet" is a tactical wall. Cues that distinguish:

| Signal | Probably a *tactical wall* (delegate) | Probably a *content gap* (don't delegate) |
|---|---|---|
| Can you write the proof on paper in <10 lines? | yes | no |
| Are you sure the statement is correct? | yes | no |
| Does the proof rely on a well-known general lemma? | yes (Mathlib has it) | no (you'd have to invent) |
| Does delegation hide an issue? | no — math is sound | yes — premature `sorry` |
| Are you grepping Mathlib for `card_inter_add_*`? | yes | n/a |

Content gaps need human work first: revise the statement, reconsider the
hypothesis, sketch the math. *Then* hand off to Aristotle for the plumbing.

## How this shapes our workflow

In [docs/aristotle-workflow.md](aristotle-workflow.md), the attempt budget
is calibrated around the wall:

* One-liners (`rfl`, `decide`, `simp`, `omega`): always try by hand —
  no wall to hit.
* Short tactical (≤10 lines, no induction): one ~5-minute hand attempt.
  If you're already grepping Mathlib at minute 5, the wall arrived;
  delegate.
* Medium (induction, list arithmetic): sketch only. The wall *will*
  arrive in the induction step or in a `Finset.card` reformulation.
* Anything bigger: delegate immediately with a `PROVIDED SOLUTION`.

Concurrency rule (file-freezing while delegated) is what makes this
work without stalls: while Aristotle plumbs, the human is on a different
file doing math content.

## For a future blog post

Pitch:

> Formal verification has a labor-division problem. The traditional
> framing — "AI helps with proofs" — is too coarse. There's a specific,
> common moment we call the *math tactical wall*: where the math is
> done and only the Lean plumbing remains. AI is much better at this
> than humans; humans are better at the math. The art of the workflow
> is recognizing the wall fast and handing off cleanly. We have a
> concrete protocol — frozen files, attempt budgets, provided-solution
> docstrings — that operationalizes this division. Here's how it
> shaped a real BFT-protocol formalization: …

Worked examples ready: Lemma 10 (round-robin pigeonhole),
`quorumIntersection` (Finset cardinality), eventual examples from
Theorems 1–4. Counter-examples (content gap, not tactical wall):
`Validation.lean` realizability lemmas (hand-proved cleanly because the
math IS the work — there's no Mathlib lemma to grep for).

## Connection to formalization workflow

Document referenced from:
- [docs/aristotle-workflow.md § Delegation policy](aristotle-workflow.md)
- [formalization.md § Where to look](../formalization.md) (TODO link)

## Companion blog seed

The conceptual side (this doc) is paired with
[blog-aristotle-integration-gotchas.md](blog-aristotle-integration-gotchas.md),
which collects the *operational* gotchas that show up after the
delegation decision (import-narrowing, `exact?` placeholders, `▸`
cast mismatches, file-freezing, bundled iteration, etc.). Together
they're the two halves of a longer post on AI-augmented Lean
formalization.
