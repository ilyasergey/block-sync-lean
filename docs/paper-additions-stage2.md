# Stage 2 — Paper-side notes from the mechanization

> Companion to [`paper-additions-stage1.md`](paper-additions-stage1.md).
> Stage 1 covers items whose Lean proofs were fully closed at its
> writing. Stage 2 records items surfaced *after* Stage 1, again
> only for items where the mechanization has settled enough to
> warrant a paper-author-facing recommendation. The companion
> [`formalization.md`](../formalization.md) remains the per-item
> proof-status table.

This stage adds one item to the previous round. It is a refinement
of finding F-8 ("validator-ID assumptions") in
[`mechanization-findings.md`](mechanization-findings.md), surfaced
when packaging the Mysticeti-Beluga liveness bundle. The paper-side
fix is a single-sentence clarification, but it is load-bearing.

---

## 1. §2 — Qualify the BFT bound: "at most `f` Byzantine *among the registered validators*"

The paper writes the BFT bound as "at most `f` Byzantine
validators" (within `f < n / 3`), and at several points in §D.2 /
§D.3 the proofs use it in the form "any quorum of `2f + 1`
distinct validators contains at least `f + 1` honest ones". The
load-bearing step is the same in both:

> *for any nodup list `S` of validators, the count of Byzantine
> entries in `S` is at most `f`.*

In the paper this reading is unambiguous because the prose's
"validators" implicitly means *registered* validators — the
universe of validators is the system's `n`-element registered set,
nothing else.

But a literal-minded formalization that lifts the bound to "for
any nodup list of `ValidatorId`s, at most `f` filter as
Byzantine" makes the implicit qualifier visible — and the bound,
without it, is *false*. A list of `f + 1` *unregistered* IDs has
every entry classify as Byzantine (since `is_honest` returns false
for unregistered IDs), trivially exceeding `f`.

**Add:** When stating the BFT bound (in §2 alongside `n` and
`f`), qualify it explicitly:

> Out of the `n` registered validators, at most `f` are Byzantine.
> Equivalently, for any subset / nodup list `S` of registered
> validators, at most `f` entries of `S` are Byzantine.

Pair this with the F-8 recommendation that the registered set has
IDs `{0, …, n − 1}`, so the universe of "registered" is itself
unambiguous.

**Why:** The paper's quorum-intersection step (used in L13, L15,
T7) silently combines two facts: that the cited list of `2f + 1`
validators is drawn from the registered set (because they are
authors of blocks in state, parents of a block, etc.) *and* that
the BFT bound applies to any registered list. Without the
"registered" qualifier on the bound, the reader has to rederive
the universe restriction at every quorum-intersection use site —
and a careful reader (or formalizer) will notice the bound itself
is false in the literal reading. Stating the qualifier once at
§2 makes the rest of the prose unambiguous and the formal bound
provable.

This sub-finding was surfaced concretely while packaging the
Mysticeti-Beluga liveness bundle: a delegation attempt to prove
"at most `f` Byzantine in any author list" as a stand-alone
invariant returned a refutation by counterexample (a list of
`f + 1` copies of an unregistered ID), confirming that the
"registered" qualifier is load-bearing rather than decorative.

---

## 2. §5 — Lemma 1 says "the same round" but the proof's content is "≥ r + 1"

Paper Lemma 1 (§5):

> *"After GST, all honest validators will enter the same round
> within 3Δ."*

The proof sketches it as a consequence of post-GST message-delay
bounds (`Δ`-bounded delivery between honest validators) plus
synchronous block dissemination. Mechanizing the lemma against an
explicit trace model exposes that the *strict* "same round" form
is stronger than what the cited assumptions actually deliver —
the lemma as stated requires either *atomic round transitions*
(all honest validators advance simultaneously) or a separate gap-0
argument that isn't in the proof sketch.

The asymmetric piece: between adjacent round advances, the trace
naturally exhibits **transient one-round skews** — when one
honest validator's local-round counter ticks from `r` to `r + 1`,
others remain at `r` until each receives the relevant blocks and
ticks themselves. These transients are bounded (the paper's
3Δ bound captures their duration), but they are not zero-duration
unless round transitions are taken to be atomic.

What the paper's proof of L1 *actually* delivers, as written, is
the weaker:

> *"After GST, given an honest validator at round `r`, every
> honest validator reaches round ≥ r + 1 within 3Δ."*

(I.e., everyone catches up to at least `r + 1`, with possibly
some validators at `r + 1` and others at `r + 2` if they raced
ahead.) This is what `SchedulerFairness` (Assumption 2,
finding F-1a's lockstep form) provides directly.

**Add:** Either:

1. **Adjust L1's wording** to match what the proof delivers:

   > *"After GST, given an honest validator at round `r`, every
   > honest validator will reach round ≥ r + 1 within 3Δ."*

   This is the form used by downstream §5 proofs (T1, T3, T4 cite
   "all honest at round r+1 by some 3Δ-bounded time", not "at the
   same exact round at every step").

2. **Or supplement L1** with a one-paragraph argument bridging the
   weaker form to the strict form, explicitly invoking either an
   atomic round-transition assumption or a "first-step-where-all-reach-r+1
   has gap = 0" structural argument.

**Why:** A reader trying to formalize L1 hits the bridge silently
— the strict same-round form has neither a stated derivation nor
a stated supporting assumption. Either fix makes the chain
explicit.

The mechanization-side adjustment was to weaken the bundle
conjunct `BelugaPostGSTLiveness.honest_round_sync` and the
`lemma1_honest_round_entry` wrapper to the "≥ r + 1" form;
their proof becomes a one-line invocation of `SchedulerFairness`.
The deviation from the paper's strict statement is recorded as
finding **F-1b** in
[`mechanization-findings.md`](mechanization-findings.md).

---

## Outlook

When the in-flight liveness rounds (paper §5 T1/T3/T4 and
paper §D.2 L8/L9/L11/L12/T6) close, Stage 3 will fold their
findings in. T1/T3/T4 are now structurally tractable from
`(h_time, h_sync, h_fair)` once the foundation lemmas
(`step_emittedOperations_monotone`, `hasProposedFor_monotone`)
are bridged with the `proposed_for_lt_currentRound` invariant
plus iterated `SchedulerFairness`; expect Stage 3 to record any
further paper-side observations the deep liveness proofs surface.
The §D.2 round may surface additional items in the same shape as
F-8(c) — implicit universe / qualifier issues exposed by literal
formalization.
