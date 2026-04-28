# Stage 3 — Recommended additions to Beluga

> Companion to [`round-02-findings.md`](round-02-findings.md), which
> records every observation from formally verifying the revised
> paper. This document is the *author-facing distillation*: a short
> list of concrete edits to consider for the next revision, in plain
> English, in the order they appear in the paper. It has no
> dependence on Lean or formal-methods background to read.

The revised paper closed six of the round-01 findings (F-2 pinning
`n = 3f+1`, F-5 enumerating the §D.3 DAG invariants, F-6 reconciling
the reputation-update timing, F-7 restating Theorem 7 as
prefix-consistency, F-8 fixing validator IDs to `{v_0, …, v_{n-1}}`,
F-11 stating block-digest determinism). Four findings remain open
paper-side, and two new wording-level observations surfaced from
the round-02 revisions to Lemma 1 and the round-advancement rules.

The recommendations below cluster into four groups:

1. **Two new wording fixes** prompted by the round-02 changes
   (Lemma 1's quantifier order, rule (iii)'s target round).
2. **Four round-01/02 findings** that did not land in round-02 and
   are worth re-iterating (F-1, F-4, F-12, F-13).
3. **An audit of the §5 partial-synchrony assumptions**: which are
   stated explicitly, which are implicit in the §4 prose, and which
   are *too strong* to follow from the protocol as written.
4. **Two structural edits to §5** that fall out of the audit.

---

## 1. New wording fixes from round-02

### 1.1. Lemma 1 — pin the quantifier order

The revised L1 reads:
> *After GST, if round `r` is the highest round that honest
> validators are in at some time `t`, then all honest validators
> will enter round `r` by `t + 4Δ`.*

The phrase *"all honest validators will enter round `r` by
`t + 4Δ`"* is read two ways:

- **simultaneous:** *"there is a time `t' ≤ t + 4Δ` at which every
  honest validator is at round `≥ r`."*
- **per-validator:** *"each honest validator is at round `≥ r`
  at some time `≤ t + 4Δ` (possibly different times)."*

The downstream uses of L1 (Theorem 3, Theorem 4, the happy-case
timing analysis) all want the *simultaneous* reading — they need a
single moment at which all honest validators are at the same round
or higher, so they can claim "all `2f+1` honest blocks for round
`r` exist by `t + 4Δ`". The per-validator reading is too weak for
this conclusion.

**Suggested wording.**

> *After GST, if round `r` is the highest round any honest validator
> is in at some time `t`, there is a time `t' ≤ t + 4Δ` at which
> every honest validator is at round `≥ r`.*

The single-`t'` quantifier makes the simultaneity unambiguous and
matches the way L1 is consumed downstream.

### 1.2. Round advancement rule (iii) — pin the target round

The revised §4.2 advancement rules read:
> *A validator `v_i` advances to round `r` if: (i) it receives `2f+1`
> blocks from round `r−1` whose creators have reputations above a
> threshold; or (ii) it is in round `r-1`, and the per-round timeout
> `T_rd` expires; or (iii) it is in round `< r−1`.*

Read literally with `r` as the target round, rule (iii) says: *if
`v_i` is in any round `< r-1`, it can advance to round `r`*. This
is a "skip-ahead" rule that lets `v_i` jump arbitrarily far up the
round ladder.

But the L1 case-2 proof reads:
> *validators in `V_slow` advance to round `r − 1` immediately and
> create their round `r-1` blocks at time `t + 3Δ`.*

Here `V_slow` consists of validators in *any* round `< r-1`, and
they all advance to round `r-1` (not `r`) and create round-`r-1`
blocks. The rule's `r` in the description is being applied with a
re-quantification: the validators advance to `(highest known round)
− 1`, not to `(highest known round)`. The §4.2 rule statement does
not surface this re-quantification.

The two readings are not equivalent for the protocol:

- **Skip-ahead.** `v_i` jumps to round `r` without creating a
  round-`r-1` block, so it does not contribute to round `r-1`'s
  `2f+1`-creator quorum. Subsequent rounds may then lack the
  `2f+1` round-`r-1` parents they need.
- **Catch-up.** `v_i` advances to `r-1`, creates a round-`r-1`
  block (joining the quorum), then proceeds with rule (i)/(ii) for
  later advances.

The L1 proof and downstream §5 reasoning need the catch-up reading.

**Suggested wording.**

> *(iii) `v_i` is in some round `r' < r-1` and observes (in its
> view) some block of round `≥ r`; in this case `v_i` advances
> directly to round `r-1` (without waiting for `T_rd` or for the
> `2f+1` round-`r-2` quorum), creates its round-`r-1` block in the
> normal way, and proceeds with rule (i) or (ii) for further
> advances.*

This makes the trigger explicit ("observed a round-`r` block") and
the target explicit (`r-1`, not `r`).

---

## 2. Four findings still open after round-02

### 2.1. (F-1) Name the §5 partial-synchrony assumption

The §5 proofs of L1, T1–T4 silently use two liveness facts that
the paper does not state explicitly:

- **Per-action prompt scheduling.** Post-GST, when an honest
  validator's protocol action becomes enabled (it has the round
  quorum to advance, or it has an acceptable block to accept), it
  performs that action within `Δ`.
- **Universal in-pool delivery.** Post-GST, every block in the
  global pool is eventually known to every honest validator —
  either via the §2 push channel (for honest authors) or via the
  §4.3 pull mechanism (otherwise).

We recommend bundling these (along with the already-stated §2
delivery and the §4.2 protocol-synchronization claim) into a single
named "Assumption" in §5, so that L1 and T1–T4 can be stated as
"under Assumption N, …" rather than letting the proofs invoke them
implicitly. See round-01's `paper-additions-stage2.md` §1 for a
concrete proposed wording. The round-02 revision does not yet
include this.

### 2.2. (F-4) Cite Assumption 1 in proofs of L4 and L5

Lemmas 4 and 5 (Appendix C.2) invoke the latency-triangle bound
implicitly when concluding "all honest validators receive each
other's round-`r` blocks within Δ post-GST". Citing Assumption 1
explicitly at the point of use clarifies the structure of the
argument; the math is correct as is, the citation is what's
missing. (Editorial only.)

### 2.3. (F-12) State T1 and T2 with the action-priority argument

The current §5 proofs of T1 (Block availability) and T2 (Causal
availability) route through ImPoA / `f+1` references / pull
reasoning. These proofs are correct, but the action priority of
§4 (`accept ≻ store ≻ advance`, all above `propose`) makes them
single-step structural facts rather than "eventually" claims. We
recommend rewriting T1 and T2 with the simpler argument; ImPoA
remains relevant in §4.3 as the *implementation* mechanism
without being load-bearing for §5 correctness. See round-01
`paper-additions-stage2.md` §3 for proposed proof sketches.

### 2.4. (F-13) State accept/store atomicity (or split with priority)

§4 prose treats `block_accept` and `block_store` as conceptually
distinct outputs; Figure 8 in Appendix E glues them into a single
`create_new_block` step. This affects T1: under atomic accept-and-
store, T1's conclusion holds at the moment of acceptance; under
split actions, T1 needs the action-priority argument from F-12.
Recommendation: either collapse into one action in Figure 8, or
split and explicitly state the action priority. Either fix
suffices.

---

## 3. Audit: which §5 assumptions are paper-stated, which are buried, which are too strong

The §5 proofs of L1 and T1–T4 rest on a small set of post-GST
liveness assumptions. From the formalization side we have to be
explicit about each — every proof needs to consume them by name.
This brought into focus *which* of these the paper already states,
which are implicit, and which are stronger than the protocol
actually delivers.

| # | Assumption (plain English) | Paper status | Recommendation |
|---|---|---|---|
| 1 | The wall clock advances monotonically and is unbounded. | Implicit in §2 timing semantics; reasonable. | No edit — the paper's timing model conveys this. |
| 2 | Post-GST, every push message between honest validators is delivered within `Δ`. | **Explicitly stated in §2.** | No edit. |
| 3 | Post-GST, the rounds of any two honest validators differ by at most one. | **Implicit.** L1's case-1 reasoning needs gap ≤ 1 starting at `t`; the round-02 revision admits gap > 1 transiently and uses the new rule (iii) to re-establish the invariant within `4Δ`. | A two-line clarification in §4.2 / §5: *"After `GST + 4Δ`, by Lemma 1, the rounds of any two honest validators differ by at most one. The §5 reasoning is conducted at this steady state."* |
| 4 | Post-GST, when an honest validator has an acceptable in-pool block (its parents are received-or-imPoA-available), it accepts the block within `Δ`. | **Implicit.** L1's proof uses "accept by `t + 3Δ`", which folds in this `Δ`-bound on acceptance after the parents arrive. The paper does not state it as a separate primitive. | State it as item 5 of the proposed §5 assumption (F-1). |
| 5 | Post-GST, every block in the global pool is eventually known to every honest validator, via push (for honest authors) or via the §4.3 pull mechanism (otherwise). | **Implicit.** This is the design intent of §4.3, but the paper sketches the pull mechanism without naming the conclusion. T2 and T4 cite "the validator eventually pulls the missing block" without stating the conclusion as a fact. | Add one sentence at the end of §4.3 naming this conclusion (proposed wording in round-01 `paper-additions-stage2.md` §4a), and state it as item 6 of the proposed §5 assumption (F-1). |
| 6 | Post-GST, when an honest validator `v_i` is at a strictly lower round than some honest validator `v_j`, then `v_i` reaches `v_j`'s round within `4Δ`. | **Derived in L1's proof.** The composition of (2), (4), (5), and §4.2 rule (i) yields exactly this `4Δ` catch-up: `Δ` for `v_j`'s block to reach `v_i`, `2Δ` for `v_i` to accept it (via push or pull/imPoA), `Δ` for the per-action scheduling of `v_i`'s rule-(i) advance. | This is what the §5-level reasoning consumes. Once items 2, 4, 5 are named, this is a direct corollary; no separate assumption needed. |
| 7 | Post-GST, every honest validator advances rounds within `Δ`, unconditionally. | **Not implied — and inconsistent with the protocol.** Rule (ii) gives a `T_rd = 5Δ` upper bound on time-in-round only when no quorum or leader-block trigger fires; without such a trigger, `Δ` is too tight. | Don't state this. Use item 6 instead. |

The audit: **items 1–6 are implied by §2 + §4.2 + §4.3 once the
implicit content (items 3, 4, 5) is named.** Item 7 is the
over-strong form the round-01 paper's §5 prose appeared to
assume; the round-02 paper correctly avoids relying on it
(in particular, L1's case-2 proof uses item 6 in disguise — Δ-
delivery + 3Δ-acceptance + immediate rule (iii) advance).

The recommended outcome is a §5 assumption that lists items
1–5 (with item 6 derivable from them), and never references
item 7.

---

## 4. Two structural §5 edits

These follow from the audit above; they are independent of
findings F-1 through F-13.

### 4.1. Decide whether Lemma 2 is gone or just repackaged

The round-01 paper's Lemma 2 ("round-to-round latency `≤ 3Δ` for an
honest validator at round `r`") is absent from the round-02 §5.
Its content (round monotonicity + the round-IVT) is folded into
Theorem 3's proof. Either:

- *Deliberate:* note in the §5 narrative that L2 has been
  consolidated into T3 (a brief footnote or remark suffices); or
- *Inadvertent:* restore L2 as a named lemma if downstream work
  cites it.

Without one of these, readers familiar with the round-01 paper may
look for L2 and not find it.

### 4.2. State the §5 assumption explicitly

This is the structural form of finding F-1. The §5 prose currently
opens with *"We prove Beluga satisfies the properties defined in
Definition 1"* and proceeds directly to L1 and T1–T4. We recommend
inserting, before L1, a short "Assumption N" paragraph naming
items 1–5 of the audit table above. The benefit:

- L1, T1–T4 can each be stated as *"under Assumption N, …"*, making
  the dependence on §4.2/§4.3 liveness explicit.
- The §5 proofs can cite "Assumption N item 5" for the in-pool-
  delivery step, instead of weaving the pull-mechanism argument
  into the §5 prose.
- Future readers and verifiers know exactly which liveness
  ingredients §5 consumes — and that the proofs do *not* rely on
  the over-strong "rounds advance within `Δ`" form.

A concrete proposed wording for the assumption is in round-01
`paper-additions-stage2.md` §1.

---

## Summary

| Section | Edit | Severity |
|---|---|---|
| §5 (L1) | Pin the quantifier order ("there is a time `t' ≤ t + 4Δ` at which every honest validator …") | **Medium** — current wording is ambiguous |
| §4.2 (rule iii) | Pin the target round and trigger ("advance to `r-1` upon observing a round-`r` block") | **High** — current wording admits an unsound skip-ahead reading |
| §5 (before L1) | State the partial-synchrony assumption (items 1–5 of the audit) explicitly | **Medium** — F-1, repeated from round-01 |
| §C.2 (L4, L5) | Cite Assumption 1 in the proof bodies | **Low** — F-4, editorial |
| §5 (T1, T2) | Restate proofs with the action-priority argument | **Low** — F-12, paper proofs are correct as is, but the simpler form is more direct |
| §4 (Figure 8) | Make accept/store atomicity explicit, or split with action priority | **Low** — F-13, editorial |
| §5 (L2) | Note whether L2 was consolidated into T3 or restore it | **Low** — round-02 transparency |
