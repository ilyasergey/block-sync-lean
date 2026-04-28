# Suggested edits to the Beluga manuscript

A short list of edits we recommend for the next revision. Each is
phrased in the paper's own notation (Sections 2, 4, 5, and
Appendices C–D); none requires background outside the manuscript.

The edits cluster into three groups: two wording fixes prompted by
the latest revision (Section 1), an explicit assumption in §5
(Section 2), and a small audit of which §5 assumptions are
paper-stated, which are implicit, and which need promoting to
named primitives (Section 3). Section 4 collects three minor
editorial points.

The goal is a *mathematically rigorous but high-level*
characterization of what is proved and what is assumed, with
minimal changes to the current manuscript.

---

## 1. Two wording fixes

### 1.1. Lemma 1 — pin the quantifier order

The current statement reads:
> *After GST, if round `r` is the highest round that honest
> validators are in at some time `t`, then all honest validators
> will enter round `r` by `t + 4Δ`.*

The phrase *"all honest validators will enter round `r` by
`t + 4Δ`"* admits two readings:

- **Simultaneous:** *there is a single time `t' ≤ t + 4Δ` at
  which every honest validator is at round `≥ r`.*
- **Per-validator:** *each honest validator is at round `≥ r` at
  some time `≤ t + 4Δ`, possibly different times for different
  validators.*

The downstream uses of Lemma 1 (Theorem 3, Theorem 4, the happy-
case timing analysis) all want the *simultaneous* reading: they
need a single moment at which all `2f + 1` honest validators
have produced round-`r` blocks. The per-validator reading is too
weak for that conclusion.

**Suggested wording.**
> *After GST, if `r` is the highest round any honest validator is
> in at some time `t`, then there is a time `t' ≤ t + 4Δ` at which
> every honest validator is at round `≥ r`.*

The single existential quantifier on `t'` makes the simultaneity
explicit and matches the way Lemma 1 is consumed throughout §5
and §C.

### 1.2. Round-advancement rule (iii) — pin the target round

The §4.2 advancement rules read:
> *A validator `v_i` advances to round `r` if: (i) it receives
> `2f + 1` blocks from round `r − 1` whose creators have
> reputations above a threshold; or (ii) it is in round `r-1` and
> the per-round timeout `T_rd` expires; or (iii) it is in round
> `< r − 1`.*

A literal reading of rule (iii) — with `r` the target — says: *if
`v_i` is in any round `< r-1`, it can advance to round `r`*. That
is, a validator may skip arbitrarily many rounds in one step.

But the proof of Lemma 1 (case 2) reads:
> *validators in `V_slow` advance to round `r − 1` immediately and
> create their round `r-1` blocks at time `t + 3Δ`.*

Here `V_slow` consists of validators in *any* round `< r-1`, and
they all advance to round `r-1` (one less than the highest known
round) and proceed to create round-`r-1` blocks. This is a
"catch-up to one below the leader" rule, not a "skip to the
leader" rule.

The two readings give different protocols:

- *Skip-ahead.* `v_i` jumps to round `r` without ever creating a
  round-`r-1` block; it does not contribute to round-`r-1`'s
  `2f + 1`-creator quorum. Subsequent rounds may then lack the
  `2f + 1` round-`r-1` parents they need to reference.
- *Catch-up.* `v_i` advances to `r-1`, creates a round-`r-1` block
  (joining the quorum), then proceeds with rules (i)/(ii) for
  later advances.

The Lemma 1 proof and downstream §5 reasoning need the catch-up
reading.

**Suggested wording.**
> *(iii) `v_i` is in some round `r' < r - 1` and observes (in its
> view) some block of round `≥ r`; in this case `v_i` advances
> directly to round `r-1` (without waiting for `T_rd` or for the
> `2f+1` round-`r-2` quorum), creates its round-`r-1` block in the
> normal way, and proceeds with rules (i)/(ii) for further
> advances.*

The trigger ("observed a block of round `≥ r`") and the target
(`r-1`) become explicit, matching the proof's usage.

---

## 2. State the §5 partial-synchrony assumption explicitly

The §5 proofs of Lemma 1 and Theorems 1–4 silently consume two
liveness facts that the manuscript currently leaves implicit:

- **Per-action prompt scheduling.** Post-GST, when an honest
  validator is in a state where the §4.2 protocol enables a local
  action — propose, accept, store, or advance — the validator
  performs that action within `Δ`.
- **Universal in-pool delivery.** Post-GST, every block in the
  global pool is eventually known to every honest validator,
  either via the §2 push channel (for honest authors) or via the
  §4.3 pull mechanism (otherwise).

Combined with the already-stated §2 push delivery, the §4.2
protocol-synchronization claim, and the §4.2 round-advancement
rules, these are exactly the ingredients §5's proofs consume.

We recommend stating them as a single named assumption at the top
of §5, of the form:

> **Assumption (Beluga partial synchrony).** Post-GST, the
> following hold:
>
> 1. *(Clock.)* Wall-clock time is non-decreasing and unbounded.
> 2. *(Delivery — §2.)* Every push message between honest
>    validators is delivered within `Δ`.
> 3. *(Round timeout — §4.2 rule (ii).)* The per-round timeout
>    `T_rd = 5Δ` upper-bounds time-in-round: an honest validator
>    advances to the next round within `5Δ` of entering its current
>    round.
> 4. *(Protocol synchronization — §4.2.)* Two honest validators'
>    rounds differ by at most one in steady state (or, equivalently
>    given Lemma 1, after `t + 4Δ` post-GST).
> 5. *(Accept-action liveness — §4.2.)* When an honest validator
>    has an acceptable in-pool block (its parents are received-or-
>    ImPoA-available), it accepts the block within `Δ`.
> 6. *(In-pool delivery — §4.3.)* Every block in the global pool
>    is eventually known to every honest validator, via push or
>    via the pull mechanism.

Items 3 and 4 are paper-stated already (timeout `T_rd` is in §4.2,
the protocol-synchronization claim is implicit in §4.2 prose).
Items 5 and 6 are the implicit additions: 5 is the per-action
half of §4.2; 6 is the design intent of §4.3, currently only
sketched. Naming them brings the §5 hypothesis chain in line with
what the proofs actually need.

Lemma 1 and Theorems 1–4 can then be stated as *"under the Beluga
partial-synchrony assumption, …"* and the §5 prose can cite Items 5
and 6 by name rather than weaving the underlying mechanism into
each proof.

---

## 3. Audit of §5 assumptions

| # | Assumption (paper notation) | Paper status | Suggested action |
|---|---|---|---|
| 1 | Wall clock advances monotonically and is unbounded. | Implicit in §2 timing semantics. | Subsume under the §5 assumption above. |
| 2 | Post-GST, every push message between honest validators is delivered within `Δ`. | **Stated in §2.** | No change. |
| 3 | The per-round timeout `T_rd = 5Δ` upper-bounds time-in-round post-GST. | **Stated in §4.2 rule (ii).** | Cite by name in the §5 assumption. |
| 4 | The rounds of any two honest validators differ by at most one in steady state. | Implicit; derivable from Lemma 1 once stated. | Note this as a corollary of Lemma 1 in the steady state, or include in the §5 assumption. |
| 5 | When an honest validator has an acceptable in-pool block, it accepts the block within `Δ`. | Implicit in §4.2 prose. | Add as Item 5 of the §5 assumption. |
| 6 | Every block in the global pool is eventually known to every honest validator (push or pull). | Implicit conclusion of §4.3. | Add one sentence at the end of §4.3 naming this conclusion, and add it as Item 6 of the §5 assumption. |
| 7 | Post-GST, when an honest validator is at a strictly lower round than some honest validator, it catches up within `4Δ`. | **Derived in the proof of Lemma 1.** Composes Items 2, 5, 6 with rules (i)/(iii). | No primitive needed; this is Lemma 1 itself. |

The audit identifies two facts (Items 5 and 6) that should be
promoted from implicit to stated. With those promotions every
ingredient consumed by §5 corresponds to a named paper assumption,
and the §5 proofs become explicit citations rather than informal
appeals to "the protocol scheduling is fast enough".

---

## 4. Three minor editorial points

### 4.1. Cite Assumption 1 in proofs of Lemmas 4 and 5

Lemmas 4 and 5 (Appendix C.2) invoke the latency-triangle bound
implicitly when concluding *"all honest validators receive each
other's round-`r` blocks within `Δ` post-GST"*. Citing
Assumption 1 explicitly at the point of use clarifies the
structure of the argument; the math is correct as stated.

### 4.2. Decide whether Lemma 2 was consolidated

Earlier versions had a Lemma 2 (round-to-round latency `≤ 3Δ`
for an honest validator) sandwiched between Lemma 1 and Theorem 1.
The current manuscript proves the same content inline inside
Theorem 3. Either restore Lemma 2 as a named statement (if it is
cited in downstream work) or add a brief footnote noting the
consolidation. Without one of these, readers familiar with the
earlier version may look for it and not find it.

### 4.3. Clarify accept/store atomicity (or split with priority)

The §4 prose treats `block_accept` and `block_store` as
conceptually distinct outputs (consensus reads `accept`; execution
reads `store`). Figure 8 in Appendix E, however, glues them into a
single `create_new_block` step. Theorem 1's argument changes
slightly between the two readings: under atomic accept-and-store
the conclusion holds at the moment of acceptance; under split
actions a one-line action-priority argument is needed.

We recommend either (a) collapsing accept and store into a single
`block_accept_and_store` action in Figure 8, or (b) keeping them
split and stating the §4.2 action priority `accept ≻ store ≻
advance` so the structural argument can be cited.

---

## Summary

| Section | Edit | Severity |
|---|---|---|
| §5 (Lemma 1) | Pin the quantifier order: *"there is a time `t' ≤ t + 4Δ` at which every honest validator is at round `≥ r`."* | **Medium** — current wording is ambiguous |
| §4.2 (rule iii) | Pin the target round and trigger: *"observes a block of round `≥ r`; advances to `r-1`."* | **High** — current wording admits an unsound skip-ahead reading |
| §5 (before Lemma 1) | State the partial-synchrony assumption (six items) explicitly | **Medium** — currently implicit |
| §4.3 | One sentence naming the pull-mechanism conclusion | **Medium** — design intent currently unstated |
| §C.2 (Lemmas 4, 5) | Cite Assumption 1 in proof bodies | **Low** — editorial |
| §5 (Lemma 2 placement) | Note consolidation into Theorem 3, or restore | **Low** — editorial |
| §4 / Figure 8 | Make accept/store atomicity explicit, or split with action priority | **Low** — editorial |
