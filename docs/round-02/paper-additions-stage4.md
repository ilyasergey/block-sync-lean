# Suggested edits to the Beluga manuscript — Stage 4

A self-contained block of amendments confined to **Appendix D**.
Sections 4 and 5 are untouched.

---

## 1. §D.2 — preamble (new paragraph at the start of §D.2)

Insert immediately before Lemma 7:

> **Assumptions consumed by §D.2.** In addition to the §5
> partial-synchrony assumption and the §4.2/4.3 protocol rules,
> §D.2 consumes the following two per-action liveness primitives,
> symmetric to the §4.2 accept-action liveness already named in §5:
>
> - **(propose-action liveness).** *Post-GST, when an honest
>   validator at round `r` has not yet proposed for `r`, it does
>   so within `Δ`.*
> - **(store-action liveness).** *Post-GST, when an honest
>   validator has accepted a block but not yet stored it, it
>   stores within `Δ`.*
>
> Both are direct mirrors of the accept-action `Δ`-bound and
> faithfully follow the §4.2 prose's symmetric treatment of the
> four protocol actions (propose, accept, store, advance).

The two primitives are paper-implicit; the §4.2 prose treats all
four actions symmetrically as per-action liveness, but only three
of the four (accept, advance via `T_rd`, and the channel itself)
are surfaced explicitly in §5.

---

## 2. §D.3 — extend the inherent-facts enumeration

The round-02 §D.3 enumerates four inherent facts (i)–(iv) that
the safety lemmas L13–L15 consume:

> *(i) Honest validators only create at most one block per round
> (i.e., honest validators do not equivocate by definition).*
>
> *(ii) Each block must reference as parents `2f+1` blocks created
> by `2f+1` distinct validators from the immediately preceding
> round.*
>
> *(iii) A block is valid only if its creator corresponds to a
> registered validator in V …*
>
> *(iv) The block digest is derived from hashing the block and can
> be used to identify the same block, where an identical digest
> implies the same block.*

Add a fifth item, surfacing a consequence of §4.2 admission
control that §D.2 derivations rely on:

> *(v) The global block pool is parent-closed: if a block `B` is
> in the accepted set of some honest validator, then for every
> parent digest `d ∈ B.parents`, the corresponding block is also
> in the accepted set of some honest validator. (Consequence of
> §4.2 admission control: an honest validator only accepts a
> block once its parents are present.)*

This makes the parent-closure of the pool an explicit fact
available to §D.2's derivations rather than a derivation hop the
reader is expected to perform.

---

## 3. §D.1.2 — tighten the leader-inclusion wording

The §D.1.2 admission rule for Mysticeti-Beluga prioritises leader
blocks among parents. Replace the priority-rule wording with the
explicit conditional form §D.2 cites:

> *(§D.1.2, leader-inclusion rule.) When an honest validator at
> round `r+1` proposes a round-`(r+1)` block, if it has accepted
> the round-`r` leader's block, that block is among the parents
> it selects.*

The current prose describes leader priority abstractly; the
conditional "accepted ⇒ included" form is what §D.2 Lemma 7's
proof actually uses.

---

## 4. §D.1.1 — sharpen footnote 6

The §D.1.1 direct-decision rule reads the certificate pattern at
round `r + 2`. Footnote 6 relates this to the §4.4 certificate
pattern. Tighten the footnote to make the equivalence explicit:

> *(§D.1.1, footnote 6, expanded.) A block `B` forms the
> certificate pattern (§4.4) precisely when its round-`(B.r + 1)`
> referencers — and equivalently its round-`(B.r + 2)`
> referencers, by the round-monotone propose-witness invariant —
> include `2f+1` distinct authors. The direct-decision rule reads
> the round-`(B.r + 2)` form; lemmas that establish the §4.4
> pattern feed the §D.1.1 rule directly.*

This pins down the conversion from "B is certified" (the §4.4
predicate) to "the round-`(B.r + 2)` cert pattern holds" (what
`directDecide` reads), removing a quiet equivalence step.

---

## 5. Cumulative amendment summary

All four edits sit inside Appendix D:

| Section | Edit |
|---|---|
| §D.2 (new preamble) | Name propose-action and store-action `Δ`-bounds as §D.2-specific assumptions. |
| §D.3 (extend item list) | Add item (v): global pool is parent-closed. |
| §D.1.2 (wording fix) | State leader-inclusion as the conditional "accepted ⇒ included". |
| §D.1.1 (footnote 6) | Make the round-`(r+1)` ↔ round-`(r+2)` cert-pattern equivalence explicit. |

Sections 4 and 5 are untouched.
