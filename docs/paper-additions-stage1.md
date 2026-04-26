# Stage 1 — Paper-side notes from the mechanization

> The companion [`formalization.md`](../formalization.md) is the
> paper→code map and per-item proof-status table — it shows
> *which* paper definitions, lemmas, and theorems are mechanized
> and *what state* each is in (✅ done · ◐ in progress · ☐ planned ·
> ⊘ out of scope · ⏸ deferred · ⚠️ proved with paper-faithfulness
> concerns). The present Stage 1 doc is the *paper-author-facing*
> distillation of that map: only the ✅-status items, in paper
> order, with a single-paragraph "what to add and why" per entry.
> Read `formalization.md` first if you want the full picture of
> what is and isn't proved; read this doc if you want the short
> list of edits to consider for the manuscript.

This document lists, in the order theorems appear in the paper,
suggested additions to the *Beluga: Block Synchronization for BFT
Consensus Protocols* manuscript that arose while formally verifying
the paper's results. **It covers only items whose Lean proofs are
fully closed at the time of writing.** Later stages will follow as
more proofs land. Each entry uses paper terminology only; no Lean
or proof-assistant content is required to read it.

A separate concern about Theorem 7's *current statement* is recorded
at the end — the closure of T7 is not yet possible without paper
edits, regardless of mechanization effort.

For more general findings (including ones not yet relevant to a
fully-closed proof) see [`mechanization-findings.md`](mechanization-findings.md).

---

## 1. §2 — Model: pin `n = 3f + 1` (or scale quorums)

The paper writes the BFT condition as `f < n / 3` (suggesting `n`
ranges freely above `3f`) and *separately* fixes the quorum size
at `2f + 1` throughout the protocol description. The standard
quorum-intersection bound

> `|A ∩ B| ≥ |A| + |B| − n = (2f + 1) + (2f + 1) − n = 4f + 2 − n`

requires `|A ∩ B| ≥ f + 1` to guarantee an honest validator in any
intersection — i.e., requires `n ≤ 3f + 1`. The two choices are
therefore consistent only at `n = 3f + 1` exactly.

The protocol *concept* works for any `n ≥ 3f + 1` provided the
quorum size scales with `n` (taking `n − f` instead of `2f + 1`):
intersection then becomes `(n − f) + (n − f) − n = n − 2f ≥ f + 1`,
and the safety arguments go through. But a literal reading of the
paper at, say, `n = 3f + 2` instantiates the protocol with quorums
of size `2f + 1 < n − f`, and the quorum-intersection step in
Lemmas 10, 13, 15 (and the proof of Theorem 7) no longer goes
through.

**Add:** State the convention. Either:
1. Pin `n = 3f + 1` exactly — then `2f + 1 = n − f` and the literal
   text is consistent; *or*
2. Replace `2f + 1` with `n − f` throughout — then the literal
   protocol scales with `n` and the safety arguments hold for any
   `n ≥ 3f + 1`.

**Why:** As written, the paper is consistent only at the boundary
case `n = 3f + 1`. A reader instantiating the protocol literally
at any larger `n` (which the `f < n / 3` notation invites) would
get a protocol whose quorum size is too small to satisfy the
intersection bound the safety proofs require. This is a
notational fix, not a protocol fix; the protocol concept is
correct for all `n ≥ 3f + 1`. The paper just needs to make the
intended quorum convention explicit.

---

## 2. §2.1 — Block structure: state digest determinism

The paper defines a block as `(r, d, author, parents, payload,
signature)` and treats `d` as an opaque field. Every uniqueness
argument in the paper (in §4.4 and §D.3) silently relies on `d`
being **determined by `(r, author)`** — i.e., two blocks with the
same `(round, author)` necessarily have the same digest.

**Add:** State that `d` is a function of `(r, author)` in §2.1
(equivalently: the digest scheme produces collisions only between
identical `(r, author)` pairs).

**Why:** Without this property, two distinct blocks by the same
author at the same round would have different digests, and the
"at most one block per `(author, round)`" arguments in §4.4 and
§D.3 would not go through.

---

## 3. §2 — Validator IDs: state that IDs are `{0, …, n − 1}`

The round-robin leader schedule (§D.1.2) defines `leader(r) =
r mod n`, which only makes sense if validator IDs are exactly
`{0, …, n − 1}`. Likewise, the digest scheme implicitly assumes
ID bounds in deriving its determinism (item 2 above).

**Add:** State that the validator set is `{0, …, n − 1}` in §2
(or equivalently: IDs are bounded by `n`).

**Why:** Without this, `leader(r)` may produce an ID that does
not correspond to any registered validator, breaking the
"three consecutive honest leaders" pigeonhole argument in §D.3
Lemma 10.

---

## 4. §4.4 — Honest non-equivocation: state both *cross-block* forms

The paper states honest non-equivocation only within a single
block ("an honest validator's block has at most one parent per
author per round"). The proof of "for any validator and round, at
most one block can become certified" (the §4.4 uniqueness
consequence) and §D.3 Lemma 13 actually rely on **two distinct
cross-block forms**:

- **(a) Cross-block parent agreement.** Any two honest-authored
  blocks in the state agree on parents at the same `(author',
  round')` pair.
- **(b) Block uniqueness.** An honest validator authors at most
  one block per `(author, round)` pair.

**Add:** State (a) and (b) explicitly alongside the within-block
non-equivocation statement in §4.4.

**Why:** Form (a) is needed because the shared honest validator
in the quorum-intersection step may have referenced the conflicting
blocks `B₁` and `B₂` from *two different blocks of theirs*, not
just within one block. Form (b) is needed in §D.3 L13's
quorum-intersection argument to identify a single honest-authored
block that references a target. The within-block form alone does
not give either.

---

## 5. §5 — Theorem 2 (Causal availability): no scheduler fairness needed

**What we proved.** Theorem 2 holds of every reachable Beluga state
*without* invoking the scheduler-fairness assumption that L1, L2,
T1, T3, T4 require (finding F-1). Causal closure is a state
invariant of Beluga: at every point in the trace, if an honest
validator has output `block_accept` for `B`, all of `B`'s causal
ancestors have already been output via `block_accept` by the same
validator.

**Add:** Note in §5 that Theorem 2 is the only Definition-1
property derivable as a *state invariant* rather than as an
"eventually" claim — it does not depend on any fairness or
liveness assumption.

**Why:** This is a useful structural distinction for readers: T2
is "free" (a structural invariant of Beluga's parent-acceptance
rule), whereas T1/T3/T4 require additional assumptions to recover
the paper's `3Δ` bounds.

---

## 6. §C.2 — Lemmas 4 and 5: cite Assumption 1 (Latency Triangle) explicitly

The paper proves Lemma 4 ("post-GST round latency is `Δ` when
honest reputations dominate") and Lemma 5 ("post-GST round latency
`2Δ`-or-blame") by invoking, in mid-proof, that "all honest
validators receive each other's round `r` blocks within `Δ`
post-GST". This step holds only by **Assumption 1 (Latency
Triangle)**, which is stated separately in §C.1 but not cited at
the point of use.

**Add:** Cite Assumption 1 explicitly in the proof bodies of L4
and L5 (or as a precondition of each lemma's statement).

**Why:** The "round latency `Δ`" step is load-bearing in both
proofs but appears as a tacit consequence; surfacing the
dependence on Assumption 1 makes the structure of the argument
explicit and matches what the formal proofs require.

---

## 7. §D.3 — Lemma 13 + Lemma 15: state the four DAG invariants used

Both Lemma 13 (certificate persistence) and Lemma 15 (uniqueness
of certified leader per round) rely on four protocol-invariant
DAG facts that the paper treats as obvious:

1. **DAG admission well-formedness.** Every block at a positive
   round has at least `2f + 1` distinct-author parents from the
   immediately preceding round, all themselves in the state.
2. **Author-round uniqueness.** Any two blocks in the state with
   the same `(author, round)` are equal (a *total* statement —
   honesty is not required, since by §4.2 a validator emits at
   most one propose per round).
3. **No equivocation in parents.** For any two blocks in the state
   that reference parents with the same `(author', round')`, the
   referenced parents coincide.
4. **Authors are registered.** Every block author corresponds to
   a registered validator.

**Add:** Promote each of (1)–(4) to a named lemma in §D.3 prior
to L13.

**Why:** Item (1) is used twice in L13's proof (at round `r + 2`
for the quorum-intersection step, then at later rounds to thread
the inductive parent reference) but is not named. Items (2)–(4)
are used in the "at least one honest validator referenced both"
step of the quorum-intersection chain in both L13 and L15.
Naming them makes the proofs explicit about which facts they
consume — useful both for clarity and for any follow-on protocol
that varies the parent-selection rule.

---

## A concern about Theorem 7's current statement

The mechanization can close Lemmas 13, 14, 15 (paper §D.3) with
no further changes to the paper. Theorem 7, however, **cannot be
closed as currently stated**, regardless of how much proof effort
is applied. The obstacle is in the statement and proof of T7
itself, not in the mechanization. Two issues compose:

### (a) "Consistent" overstated as "identical"

The proof of Theorem 7 begins:

> *"By Lemma 16, all honest validators decide a consistent status
> for each round leader block, meaning that all honest validators
> decide identical to-commit leader blocks."*

Lemma 16 establishes only **consistency** of the consensus view —
no two honest validators commit *non-Undecided* values that
disagree. It does **not** establish that all honest validators
have *identical* views: two honest validators may legitimately
differ on which leader blocks they have already decided (one ahead
in the schedule, the other still `Undecided` on slots the leader
has committed). That difference is a liveness phenomenon, not a
safety one.

To bridge "consistent views" to "identical views" you need:

> *(decision completeness)* For any two honest validators `v_i,
> v_j` and any digest `d`: `v_i` has decided `d` iff `v_j` has
> decided `d`.

Decision completeness is **not** a safety property. It is the
*liveness* claim "all honest validators eventually decide the
same slots", which the protocol satisfies after GST + bounded
delay, but only as a consequence of the consensus *liveness*
theorems (Theorem 6 and the lemmas of §D.2).

### (b) "Transaction ordering respects view equality" hides a definition

The proof continues:

> *"According to the consensus logic employed by Mysticeti-Beluga,
> all honest validators will order to-commit leader blocks and
> their causal history block consistently."*

This sentence is treating `order` as an independent observable
that "respects view equality". In a literal reading, you would
need a hypothesis of the form

> *if `view(v_i) = view(v_j)` (everywhere), then `order(v_i)`
> and `order(v_j)` are consistent prefixes of each other.*

In the paper's actual treatment, `order` is *computed* from the
consensus output by walking the causal histories of `to-commit`
leader blocks in a canonical order. So `order` is a *function of
the view*, not a separate object — and the "respects view
equality" claim is then by construction (equal inputs → equal
outputs), not an additional hypothesis. The paper does not state
this functional dependence anywhere.

### Recommended fix

Two changes to the paper, both load-bearing:

1. **State decision completeness as a named lemma in §D.2.**
   Derive it from Lemmas 11 ("any undecided leader block
   eventually gets decided") and 12 ("a block referenced by
   `2f + 1` blocks is eventually output by every honest
   validator") together with Theorem 6. Cite this lemma
   explicitly in the proof of Theorem 7 to bridge L16's
   consistency to identity.

2. **Define `order` explicitly as a function of `view`.** In §D.1
   (or at the start of §D.3), state the canonical commit-walk
   procedure that takes the view's `to-commit` decisions and
   produces a transaction sequence per validator. Theorem 7's
   "consistent ordering" then follows by:
   - L16 + decision completeness ⇒ identical views,
   - identical views + `order = canonical(view)` ⇒ identical
     orders ⇒ trivially consistent.

Without these two additions the proof of T7 has nowhere to land:
neither the consistency-to-identity step nor the
view-to-order step is justified by a paper-stated fact, and both
are necessary for the conclusion.

---

## Summary

| Paper § | Suggested addition | Severity |
|---|---|---|
| §2 | Pin `n = 3f + 1` (or scale quorums) | **High** — quorum-intersection argument fails otherwise |
| §2.1 | State `d = digest(r, author)` | **Medium** — uniqueness arguments fail otherwise |
| §2 | State validator IDs are `{0, …, n − 1}` | **Medium** — round-robin & digest depend on it |
| §4.4 | State two cross-block forms of honest non-equivocation | **Medium** — proofs of `certified_unique` and L13 use them |
| §5 (T2) | Note T2 needs no fairness | **Low** (clarification only) |
| §C.2 (L4, L5) | Cite Assumption 1 in proof bodies | **Low** — clarity, not correctness |
| §D.3 (before L13) | Name the four DAG invariants used by L13 + L15 | **Medium** — load-bearing facts that should be lemmas |
| §D.2 + §D.3 (T7) | Define `order = canonical(view)` and state decision completeness | **High** — T7 unprovable as stated otherwise |
