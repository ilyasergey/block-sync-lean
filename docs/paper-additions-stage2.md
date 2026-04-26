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

## Outlook

When the in-flight liveness rounds (paper §5 L1/L2/T1/T3/T4 and
paper §D.2 L8/L9/L11/L12/T6) close, Stage 3 will fold their
findings in. The current expectation is that the §5 rounds will
add a paper-side note about the lockstep form of Assumption 2
(finding F-1a) once they're proven from `belugaTrace`, and the
§D.2 round may surface additional items in the same shape as this
one — implicit universe / qualifier issues exposed by literal
formalization.
