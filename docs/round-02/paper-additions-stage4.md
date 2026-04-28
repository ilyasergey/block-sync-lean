# Suggested edits to the Beluga manuscript — Stage 4

A block of amendments to **Appendix D**.

---

## 1. §D.2 — preamble naming the additional fact

Insert at the start of §D.2 (before Lemma 7):

> *Beyond the assumptions of the §5 theorems, the §D.2
> derivations rely on one further inherent fact about Beluga: the
> global block pool is parent-closed — if a block `B` is in the
> accepted set of some honest validator, then for every parent
> digest `d ∈ B.parents`, the corresponding block is also in the
> accepted set of some honest validator. (Consequence of §4.2
> admission control: an honest validator only accepts a block
> once its parents are present.)*

---

## 2. §D.1.2 — tighten the leader-inclusion wording

Replace the abstract priority wording with the conditional form:

> *(§D.1.2, leader-inclusion rule.) When an honest validator at
> round `r+1` proposes a round-`(r+1)` block, if it has accepted
> the round-`r` leader's block, that block is among the parents
> it selects.*

---

## 3. §D.1.1 — sharpen footnote 6

Make the §4.4 ↔ round-`(r+2)` cert-pattern equivalence explicit:

> *(§D.1.1, footnote 6, expanded.) A block `B` forms the
> certificate pattern (§4.4) precisely when its round-`(B.r + 1)`
> referencers — and equivalently its round-`(B.r + 2)`
> referencers, by the round-monotone propose-witness invariant —
> include `2f+1` distinct authors. The direct-decision rule reads
> the round-`(B.r + 2)` form; lemmas that establish the §4.4
> pattern feed the §D.1.1 rule directly.*

---

## 4. Cumulative amendment summary

| Section | Edit |
|---|---|
| §D.2 (preamble) | Surface the parent-closure of the global block pool as the one inherent fact §D.2 needs beyond the §5 assumptions. |
| §D.1.2 (wording fix) | State leader-inclusion as the conditional "accepted ⇒ included". |
| §D.1.1 (footnote 6) | Make the round-`(r+1)` ↔ round-`(r+2)` cert-pattern equivalence explicit. |
