# Mechanization findings — for the Beluga authors

A running log of observations about the Beluga paper that surfaced
while formally verifying its theorems. Each entry is written in the
paper's own terminology — no proof-assistant background needed —
and is intended to be self-contained enough to fold back into the
paper if you choose.

We distinguish three categories:

- **Missing assumption.** A claim in the paper does not follow from
  the explicit assumptions; an additional hypothesis is needed (and
  appears to be the one the prose silently relies on).
- **Scope-pinning.** The paper's statement is correct in a special
  case (e.g. `n = 3f + 1`) but ambiguous in the general case the
  notation suggests; we recommend pinning it.
- **Surfaced invariant.** A protocol fact the paper treats as
  obvious that the proof of a stated theorem actually relies on; we
  recommend stating it as a lemma.

Findings are listed in **decreasing order of importance**.

## Summary

| ID | Severity | Category | Affected | Headline | Recommended action |
|---|---|---|---|---|---|
| **F-1** | High | Missing assumption | §5 L1, L2 (and downstream §5 T1–T4) | Paper's `3Δ` round-synchronisation bound does not follow from the stated assumptions; prose proofs silently use a *scheduler-fairness* step. | Add **Assumption 2 (scheduler fairness)** stating honest validators act within Δ of becoming enabled. |
| **F-7** | High | Missing assumption (safety/liveness boundary) | §D.3 T7 | T7's prose proof equates "consistent views" (L16) with "identical views" (needs liveness) and treats `order` as separable from `view` (it isn't). Two non-paper ingredients hidden in one short paragraph. | Either weaken T7's conclusion to prefix-consistency on the *intersection* of decided positions, or import decision-completeness from §D.2 explicitly. |
| **F-5** | Medium | Surfaced invariant | §D.3 L13, L16, T7 | Each proof relies on a protocol fact the paper takes as obvious — cert-base parents, DAG-parent connectivity, view-traceback to leader blocks, decision completeness. None are stated as lemmas. | Promote each to a named lemma in §D.3. |
| **F-2** | Medium | Scope-pinning | §2 (model), used throughout | The `\|A∩B\| ≥ f+1` bound for two `(2f+1)`-quorums only holds at `n = 3f+1` exactly; the paper writes `f < n/3` but uses fixed `2f+1` quorums uniformly. | Pin `n = 3f+1` explicitly, or scale quorum size to `n − f`. |
| **F-3** | Medium | Surfaced invariant | §4.4 (uniqueness consequence) | Paper's "honest validators don't equivocate" is stated within-block; the uniqueness proof needs the *cross-block* form (any two honest blocks agree on parents at the same `(author, round)`). | State the cross-block form alongside the within-block form. |
| **F-4** | Low | Surfaced invariant (naming) | §C.2 L4, L5 | Proofs of L4/L5 invoke Assumption 1 (latency triangle) implicitly to derive per-round Δ advancement. | Cite Assumption 1 explicitly, or state the round-advancement corollary as a named consequence. |
| **F-8** | Low | Notational hygiene | §D.1.2 (round-robin), §D.3 L10 | `r mod n` round-robin presumes validator IDs are exactly `{0, …, n−1}`; the paper takes this as obvious. | State that the validator set has IDs `{0, …, n−1}`, or reformulate the schedule via a list index. |
| **F-6** | Low | Editorial | §4.2 prose vs Figure 8 | Reputation-update trigger is `r−1` in the prose and `r−2` in the pseudocode (off-by-one due to round-increment timing). | Align prose and pseudocode. |

Each entry has a stable identifier (`F-N`) so we can refer to them
across documents.

---

## F-1. Missing assumption: scheduler fairness for Lemmas 1 & 2

**Affected statements.** Paper §5, Lemma 1 ("after GST, all honest
validators will enter the same round within `3Δ`") and Lemma 2
("after GST, if an honest validator enters round `r` at time `t_r`
and all honest validators have created and disseminated their round
`r` blocks by time `t_r`, then all honest validators will be able
to enter round `r+1` by time `t_r + 3Δ`").

**Finding.** Neither lemma follows from the paper's explicit
assumptions. The prose proofs use an implicit
**scheduler-fairness** step — "the validator processes the block /
advances its round / executes its local action *promptly*" — that
is not stated anywhere.

**Counterexample at the paper's level of abstraction.** Take
`n = 4`, `f = 1`, four honest validators, GST = 0, Δ = 10. Suppose
post-GST the network behaves as the paper assumes (every
honest-to-honest message delivered within Δ). However, the local
processing schedule is asymmetric: validator `v_0` runs continuously
and reaches round 1 by time 5, while `v_1, v_2, v_3` are not given
CPU time during the interval `[0, 30]` and so take no local action
during that window. At time `30 = GST + 3Δ`, `v_0` is in round 1
and `v_1, v_2, v_3` are still in round 0 — Lemma 1 is violated.

**Where the prose proof hides it.** Sentences such as

> "By Assumption 1 (latency triangle), if `v_i` is honest and sends
> `B_i^{r-1}` to `v_j`, then `v_j` receives `B_i^{r-1}` directly
> before receiving it via an intermediate validator … hence `v_j`
> accepts `B_i^{r-1}` …"

silently equate "`v_j` *receives* the block within Δ" (true under
Assumption 1) with "`v_j` *processes* the block within Δ" (requires
scheduler fairness). Same equivocation in:

> "they can accept these blocks via the pull protocol within `2Δ`."

**Suggested fix.** State explicitly:

> **Assumption 2 (scheduler fairness).** Post-GST, whenever an
> honest validator `v` is in a state where the protocol of §4
> enables a local action (propose, accept, store, or advance), `v`
> performs that action within Δ of becoming enabled.

Under this assumption, the paper's prose proofs of L1 and L2 go
through as written. We considered weaker variants (eventual
liveness without rate bound) but only the "within Δ" version
recovers the tight `3Δ` bound.

**Detailed write-up.** See
[paper-feedback-l1-l2-fairness.md](paper-feedback-l1-l2-fairness.md)
for full discussion, formal counterexample trace, and discussion of
where the prose silently relies on the assumption.

---

## F-7. Theorem 7's prose proof slips a liveness step into a safety claim

**Affected statement.** Paper §D.3, Theorem 7 (consensus safety).

**Finding.** The paper's prose proof of Theorem 7 begins:

> "By Lemma 16, all honest validators assign *identical* decisions
> to each leader block. Combined with the fact that transaction
> ordering respects view equality, we obtain consistent transaction
> orders."

There are two distinct issues hiding in this short argument.

### F-7a. "Identical" overstates Lemma 16

Lemma 16 establishes only **consistency** of the consensus view —
no two honest validators commit *non-Undecided* values that
disagree. It does **not** establish that all honest validators
have *identical* views: two honest validators may legitimately
differ on which leader blocks they have already decided (one ahead,
the other still `Undecided` on slots the leader has committed).
That difference is a liveness phenomenon, not a safety one.

To bridge "consistent views" to "identical views" you need:

> *(decision completeness)* For any two honest validators `v_1,
> v_2` and any digest `d`: `v_1` has decided `d` iff `v_2` has
> decided `d`.

Decision completeness is **not** a safety property. It is the
*liveness* claim "all honest validators eventually decide the same
slots", which the protocol satisfies after GST + bounded delay,
but only as a consequence of the consensus *liveness* theorems
(Theorem 6 and the lemmas of §D.2).

### F-7b. "Transaction ordering respects view equality" hides a definition

The paper writes as if `order(v)` is an independent observable
that "respects view equality". In a literal model where `view` and
`order` are introduced as separate entities, you would need a
hypothesis of the form

> *if `view(v_1) = view(v_2)` (everywhere), then `order(v_1)` and
> `order(v_2)` are prefixes of each other.*

In the paper's actual treatment, `order` is *computed* from the
consensus output (walking causal histories in a canonical order
of leader-block commits), so it is determined by the view rather
than a separate object. The "respects view equality" claim is
trivially true once `order` is understood as a function of `view`.

This isn't a paper *bug*; it's a hidden definitional move. A
reader who tries to mechanize T7 by introducing `view` and `order`
as separate entities will need this glue lemma, but it has no
counterpart in the paper because the paper never separated them
in the first place.

### Why both matter together

Stated as it stands, Theorem 7 advertises itself as a pure safety
result, but a literal proof of its conclusion (prefix-of-each-other
between any two honest orders, i.e., total agreement on the
intersection plus prefix-extension on the symmetric difference)
needs

1. A **liveness** ingredient (decision completeness — F-7a), and
2. An **implicit definitional** ingredient (order-from-view —
   F-7b)

neither of which is named in the proof prose. A verification
effort that treats T7 as standalone will produce an incorrect
proof.

### Suggested fixes

We recommend one of:

1. **Restate T7's conclusion** to a form that depends only on
   the safety part of L16: e.g.

   > *For any two honest validators `v_1, v_2` and any position
   > `k` for which both have committed transactions, the `k`-th
   > transactions agree.*

   That is, prefix-consistency on the *intersection* of decided
   positions, rather than the full prefix relation. This is what
   atomic-broadcast safety actually means.

2. **Keep the prefix-of-each-other formulation but make the
   liveness import explicit:** state T7 with decision completeness
   as a named premise and cite Theorem 6 / §D.2 for its
   discharge.

3. **Make the order-from-view definition explicit** in §D.3 (one
   sentence: "`order(v)` is the canonical traversal of the
   causal history of `v`'s committed leader blocks") so that
   F-7b becomes a non-issue.

Most BFT papers adopt one of these stances implicitly. We suggest
being explicit about which.

---

## F-5. Surfaced invariants: protocol facts assumed in safety proofs

**Affected statements.** Paper §D.3 (Mysticeti-Beluga safety),
Lemma 13 (certificate persistence), Lemma 16 (consistent
leader-status decision), Theorem 7 (consensus safety).

**Finding.** Each proof relies on a protocol invariant the paper
treats as obvious but doesn't formally state. Mechanizing the
proofs forced these out:

1. **Cert-base (used in L13).** *In round `B.r + 2`, every block
   in the DAG references at least one certificate for `B` as a
   parent.* This is the conclusion of the quorum-intersection
   argument applied at the certificate round, but the paper's L13
   proof skips directly from "`2f+1` certificates exist" to
   "every later block reaches one" without naming this step.
2. **DAG-parent connectivity (used in L13).** *Every block in a
   round later than `B.r + 2` has at least one parent in the
   state from the immediately preceding round.* Used as the
   inductive step. Implied by the protocol's parent-selection
   rule but not stated as a lemma.
3. **View-traceback (used in L16).** *Every non-`Undecided`
   honest view on a digest `d` traces back to a leader block
   `B` with `B.d = d` whose `directDecide` is non-`Undecided`.*
   Captures the protocol invariant that all consensus decisions
   originate from direct DAG-pattern observations on leader
   blocks.
4. **Decision completeness (used in T7).** *If one honest
   validator's view on a digest is `Undecided`, then all honest
   validators' views on that digest are `Undecided` (and vice
   versa).* This is the liveness-derived property that honest
   validators eventually all decide the same way. (See F-7a — we
   flag this separately as a safety/liveness boundary issue.)

**Suggested fix.** Each is candidate material for a named lemma in
§D.3. Items (1) and (2) follow from the DAG protocol structure;
items (3) and (4) follow from §D.1's decision rules and the
liveness theorems respectively.

---

## F-2. Scope-pinning: quorum-intersection bound at `n = 3f + 1`

**Affected statement.** Implicit in §2 (BFT model: `f < n/3`) and
used throughout: any two `(2f+1)`-quorums intersect in at least
`f + 1` validators (and hence at least one honest validator if
`|A ∩ B| ≥ f + 1`).

**Finding.** The intersection bound `|A ∩ B| ≥ f + 1` follows from
inclusion-exclusion only when `n = 3f + 1` exactly:

`|A ∩ B| ≥ |A| + |B| − n = (2f+1) + (2f+1) − (3f+1) = f + 1.`

For `n > 3f + 1` (still satisfying `f < n/3`) the bound becomes
`|A ∩ B| ≥ 4f + 2 − n`, which can be smaller than `f + 1`. The
paper writes `f < n/3` but uses `2f + 1` quorums uniformly,
implicitly fixing the quorum size rather than scaling it with `n`.

**Suggested fix.** Either (a) pin `n = 3f + 1` explicitly in the
model (matches the paper's worked examples and is unambiguous), or
(b) replace `2f + 1` with `n − f` in the protocol description so
the intersection bound holds for all `n ≥ 3f + 1`.

We chose option (a) for the formalization since it matches the
paper's intent without changing protocol numbers.

---

## F-3. Surfaced invariant: cross-block honest non-equivocation

**Affected statement.** Paper §4.4, the uniqueness consequence
("for any validator and round, at most one block can become
certified").

**Finding.** The proof requires that *any two honest-authored
blocks in the state agree on parents at the same `(author, round)`*
— i.e., honest validators don't equivocate *across blocks*. The
paper states honest non-equivocation only within a single block
("an honest validator's block has at most one parent per author"
or similar in-block phrasings). The cross-block form is what
discharges the case where the shared honest validator authored
two distinct blocks each referencing one of two certified
candidates.

**Suggested fix.** Strengthen the protocol assumption to:

> An honest validator never proposes two blocks that disagree on
> the parent set at any `(author, round)` it includes.

The paper appears to assume this implicitly when arguing
"honest validators behave consistently" but does not state it as
a separate condition.

---

## F-4. Surfaced invariant: implicit use of Assumption 1 in L4 & L5

**Affected statements.** Paper Appendix C.2, Lemma 4 (round
latency `Δ` when honest reputations dominate) and Lemma 5
(deterministic part — round latency `2Δ` or some malicious
validator is blamed).

**Finding.** The proofs of L4 and L5 invoke Assumption 1 (latency
triangle) implicitly, deriving the per-round `Δ` advancement bound
from "post-GST, the slowest honest validator's round advances
within `Δ`". This is the conclusion of Assumption 1 specialised to
round advancement, but the proof prose treats it as immediate.

**Suggested fix.** Cite Assumption 1 explicitly in the proofs of
L4 and L5, or state a derived corollary

> *Post-GST, if all honest validators are at round `r`, they all
> reach round `r + 1` within `Δ`,*

as a named consequence of Assumption 1 used by L4, L5.

This is a minor expositional issue; the math is correct, the
invocation just isn't named.

---

## F-8. Round-robin schedule presumes contiguous validator IDs

**Affected statement.** Paper §D.1.2, round-robin leader schedule
(`leader_of(r) := validators[r mod n]`), and Lemma 10 (round-robin
pigeonhole).

**Finding.** The round-robin formula `r mod n` produces a numeric
identifier in `{0, …, n−1}`. For "the leader of round `r`" to be a
*registered validator*, the validator set must be indexed by exactly
that range — i.e., the validators carry IDs `0, 1, …, n−1`. The
paper takes this as obvious; the formalization made it visible
because we model `system.validators : List (ValidatorId × Bool)`
allowing arbitrary ID assignment, which means `r mod n` could
otherwise produce an ID that nobody has, in which case
`isHonestValidator(r mod n)` returns `false` for every leader and
the pigeonhole conclusion fails vacuously.

**Suggested fix.** State explicitly that `system.validators`'s ID
column is `{0, …, n−1}` (perhaps in §2 alongside `n` and `f`), or
formulate the round-robin schedule directly in terms of indices into
the validator list rather than via `r mod n` of an externally
supplied ID. Either is fine; just pin one.

This is a trivial finding compared to F-1 / F-7 — purely a
notational hygiene issue. Recording it for completeness.

---

## F-6. Reputation-update timing (`r − 1` vs. `r − 2`)

**Affected location.** Paper §4.2 prose vs. Figure 8 lines 24–29.

**Finding.** The §4.2 prose says "`B.watermark[j] = r − 1`
triggers the reputation increase"; Figure 8 line 27 (or
thereabouts) says `B'.watermark[j] == r − 2`. The discrepancy is
an off-by-one due to whether the rule is invoked *before* or
*after* the round counter is incremented.

**Suggested fix.** Align the prose with the pseudocode (or vice
versa); both are consistent if the rule is invoked at the
right moment relative to round increment, but as written they
read as contradictory.

This is plausibly already obvious to anyone implementing the
protocol — flagging only because it surfaced as a confusion point.

---

## Conventions

- Findings get a stable identifier (`F-N`) the moment they are
  recorded, even if later resolved.
- Resolved findings stay in this document with a "Resolved" note
  appended, so the audit trail is preserved.
- Each entry is paper-terminology-only and self-contained — no
  references to Lean, mechanization tooling, or our internal
  module structure. Sister documents (e.g.,
  [paper-feedback-l1-l2-fairness.md](paper-feedback-l1-l2-fairness.md))
  may go deeper on individual findings.

If a future finding warrants its own deep-dive document
(like F-1 has), open a new `docs/paper-feedback-<topic>.md` and
link it from the entry here.
