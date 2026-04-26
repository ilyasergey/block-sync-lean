# Mechanization findings — for the Beluga authors

A running log of observations about the Beluga paper that surfaced
while formally verifying its theorems. Each entry is written in the
paper's own terminology — no proof-assistant background needed —
and is intended to be self-contained enough to fold back into the
paper if you choose.

The Category column captures the kind of fix we recommend (missing
assumption, scope-pinning, surfaced invariant, notational hygiene,
editorial); each finding's narrative section below the summary
table explains the specific issue and proposed change in full.

Findings are listed in **decreasing order of importance**.

## Summary

Findings are grouped by status. Within each group, listed by severity.

**Status legend:**

- ✅ **Resolved** — hypothesis explicit / invariant named **and** proofs
  go through (or, for documentation findings, the choice has been
  settled).
- ◐ **Pending** — statement-level fix in place (hypothesis surfaced or
  restatement applied), but proofs / derivation aren't all closed yet.
- ⚠️ **Open** — not addressed yet.

### ⚠️ Open

| ID | Severity | Category | Affected | Headline | Recommended action | Our address |
|---|---|---|---|---|---|---|
| **F-7** | High | Missing assumption (safety/liveness boundary) | §D.3 T7 (still); T6 (separate `order` axiom resolved) | T7's prose proof equates "consistent views" (L16) with "identical views" (needs liveness — F-7(a)) and treats `order` as separable from `view` (it isn't — F-7(b)). Two non-paper ingredients hidden in one short paragraph. | Either weaken T7's conclusion to prefix-consistency on the *intersection* of decided positions, or import decision-completeness from §D.2 explicitly. For F-7(b): define `order` as a function of state. | **F-7(b) closed for T6** via the *acceptance-history-based* `Beluga.belugaTransactionOrder` + `accepted_implies_in_belugaTransactionOrder` (both sorry-free) — sufficient for T6's liveness claim ("every accepted tx eventually appears"). **T7 needs a different `order` definition**: a *view-based* commit-walk of decided leaders, since T7's consistency claim ("two honest validators with the same view have prefix-consistent orders") cannot be discharged from acceptance history alone. That order is downstream of the Mysticeti consensus protocol's commit rule, which we model abstractly via `view : ConsensusView`. **Status:** F-7(b) for T7 is *partially specified* (acceptance-based order isn't the right shape; view-based order requires defining `order = orderOfView view` against the Mysticeti commit rule) — left for a future round once the consensus protocol's order-derivation is concretely modelled. F-7(a) remains a liveness-derived fact awaiting §D.2's L11 + L12 (in-flight bundle round `03f5fe3f`). |

### ◐ Pending

| ID | Severity | Category | Affected | Headline | Recommended action | Our address |
|---|---|---|---|---|---|---|
| **F-1** | High | Missing assumption | §5 L1, L2 (and downstream §5 T1–T4) | Paper's `3Δ` round-synchronisation bound does not follow from the stated assumptions; prose proofs silently use a *scheduler-fairness* step. | Add **Assumption 2 (scheduler fairness)** stating honest validators act within Δ of becoming enabled. | Surfaced as `SchedulerFairness` hypothesis on L1, L2, T1–T4, and the Beluga corollary. Proofs *under that hypothesis* are queued (in flight). |
| **F-1a** | High | Sub-finding of F-1 | §5 L2 derivation | The round-level shadow of Assumption 2 actually needed by L2 is the **lockstep** form (`≥ r + 1` within `3Δ`), not the catch-up form (`≥ r` within `3Δ`). The catch-up form is too weak to give L2's "round `r + 1` within `3Δ`" conclusion. | State Assumption 2's round-level corollary in lockstep form. | `SchedulerFairness` in `Beluga/Theorems.lean` is now the lockstep variant; L2 (`honest_round_advance`) is derived inline from it via the new `round_intermediate_value` helper. |
| **F-1b** | High | Sub-finding of F-1 | §5 L1 statement | Paper L1 says "all honest validators will enter the same round within 3Δ" — the strict same-round (gap-0) form. Our trace model has a gap-1 currentRound invariant (max−min ≤ 1) but not a gap-0 one: `step` advances one validator at a time, so transient gap-1 states are unavoidable between adjacent round advances. The strict form is therefore **unprovable from `(h_time, h_sync, SchedulerFairness)` alone**; it requires either atomic round transitions in the model or the gap-0 argument that the *first* step at which all reach `r + 1` has gap = 0 (which itself relies on a gap-1 invariant we have not yet formalised). | Either weaken L1's claim to "all honest reach round `≥ r + 1` within 3Δ" (the lockstep-progress form), or strengthen the trace model. We chose the former. | Bundle conjunct `BelugaPostGSTLiveness.honest_round_sync` (and the matching `lemma1_honest_round_entry` wrapper) now state the weakened form: ∀ honest reference at round r post-GST, ∃ k' within 3Δ at which all honest are at round ≥ r+1. This is exactly `SchedulerFairness`'s content surfaced as a structural property of the trace; proof is a one-line `h_fair` call. |

### ✅ Resolved

| ID | Severity | Category | Affected | Headline | Recommended action | Our address |
|---|---|---|---|---|---|---|
| **F-2** | Medium | Scope-pinning | §2 (model), used throughout | The `\|A∩B\| ≥ f+1` bound for two `(2f+1)`-quorums only holds at `n = 3f+1` exactly; the paper writes `f < n/3` but uses fixed `2f+1` quorums uniformly. | Pin `n = 3f+1` explicitly, or scale quorum size to `n − f`. | `n = 3 * f + 1` explicit hypothesis on `quorumIntersection`, `certified_unique`, `lemma15_unique_cert`, `lemma10_round_robin_pigeonhole`; all proved. |
| **F-3** | Medium | Surfaced invariant | §4.4 (uniqueness consequence), §D.3 L13 | Paper's "honest validators don't equivocate" is stated within-block; uniqueness proofs need both: **(a)** the cross-block parent-set agreement form, and **(b)** the block-uniqueness form (an honest validator authors at most one block per `(author, round)` pair). | State both forms alongside the within-block form. | Form (a) as `NoEquivocationInParents` (used by `certified_unique`); form (b) as `h_honest_unique` on L13. Both proved sorry-free under the hypotheses; **for `belugaTrace`, both are now derived sorry-free** (no honesty needed, even) from `BlockInv.uniquePropose` via `Mysticeti.MysticetiSafetyInv` (see F-5 row). |
| **F-5** | Medium | Surfaced invariant | §D.3 L13 + L15 | Each proof relies on protocol-invariant DAG facts the paper takes as obvious — DAG admission well-formedness (cert-base parents + parent-set distinct authors), author-round uniqueness, no-equivocation in parents, authors-are-registered. None are stated as lemmas. | Promote each to a named lemma in §D.3. | Closed for the `belugaTrace` instantiation. The `MysticetiSafetyInv` bundle ([`Mysticeti/SafetyInvariant.lean`](../BlockSynchroniser/Mysticeti/SafetyInvariant.lean)) packages all four conjuncts as a single trace invariant — `admission` (via `belugaTrace_admissionWellFormed`), `uniqueByAuthorRound`, `noEquivocation`, `authorsValid` — and `belugaTrace_satisfies_mysticetiSafetyInv` proves the bundle sorry-free. The belugaTrace-specialised wrappers `lemma13_cert_persistence_belugaTrace` and `lemma15_unique_cert_belugaTrace` retain only the genuine BFT side conditions (`hN`, `h_byz_bound`, `hids`). The originally listed "view-traceback" and "decision-completeness" facts are *not* DAG invariants — they concern external `view`/`order` parameters, and are tracked under F-7 instead. |
| **F-11** | Medium | Notation / definition | §2.1 block structure | Block digest `B.d` is treated as a primitive field, but every uniqueness argument silently relies on it being a *function of `(B.r, B.author)`* — i.e., the digest is determined by who wrote the block and at what round. | Define `B.d` as a function of `(r, author)` rather than a free field, or state the determinism as a named hypothesis. | `BlockInv` (in `causal_history` invariant chain) carries `B.d = digest system B.r B.author` as a trace invariant; `digest_injective` derived. |
| **F-4** | Low | Surfaced invariant (naming) | §C.2 L4, L5 | Proofs of L4/L5 invoke Assumption 1 (latency triangle) implicitly to derive per-round Δ advancement. | Cite Assumption 1 explicitly, or state the round-advancement corollary as a named consequence. | `LatencyTriangle` explicit hypothesis on L4 and L5; both proved sorry-free. |
| **F-8** | Low | Notational hygiene | §D.1.2 (round-robin), §D.3 L10, §4.2 (digest), §2 (BFT bound) | Three related ID-bound assumptions are silent: **(a)** `r mod n` round-robin presumes IDs are exactly `{0, …, n−1}` (used by L10); **(b)** `digest`'s injectivity presumes IDs are bounded by `n+1` (used by trace-invariant proofs); **(c)** the "at most `f` Byzantine" bound is implicitly *over the registered validator set* — for an arbitrary list of `ValidatorId`s the bound trivially fails (a list of `f+1` unregistered IDs satisfies `isHonest = false` for all entries). See also: paper-additions-stage2 doc. | State that the validator set has IDs `{0, …, n−1}` (covers (a), (b)) and qualify the BFT bound as "for any subset/list of *registered* validators" (covers (c)). | Form (a) as `h_ids` on L10; form (b) as `ValidIds` in the `Beluga/Protocol.lean` trace-invariant chain; form (c) surfaced by the (failed) `byz_bound` conjunct of `MysticetiPostGSTLiveness` — restructured to take a registered-list-restricted hypothesis instead. |
| **F-6** | Low | Editorial | §4.2 prose vs Figure 8 | Reputation-update trigger is `r−1` in the prose and `r−2` in the pseudocode (off-by-one due to round-increment timing). | Align prose and pseudocode. | Followed the prose (`r-1`); flagged in `formalization.md`'s "Notes on paper consistency" section. |

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

### F-1a. Round-level corollary needed in *lockstep* form (`≥ r + 1`)

When discharging Assumption 2 to a round-level fact about
`belugaTrace`, the *catch-up* form

> post-GST, when some honest validator reaches round `r`, every
> honest validator reaches round `r` within `3Δ`

is too weak to derive Lemma 2 (which concludes "round `r + 1` within
`3Δ`"). The form actually needed is the **lockstep** variant

> post-GST, when some honest validator reaches round `r`, every
> honest validator reaches round `r + 1` within `3Δ`,

which corresponds to the per-action assumption being applied through
*one full §4 round transition* (advance + propose + accept + advance)
rather than just enough actions to catch up. The `+ 1` captures the
combined effect of the §4 `allProposedFor` gate and per-action
scheduler fairness: in `3Δ` not only does everyone catch up, but the
leader also advances.

**Our address.** `SchedulerFairness` in
[`Beluga/Theorems.lean`](../BlockSynchroniser/Beluga/Theorems.lean) is
the lockstep variant. L2 (`honest_round_advance`) is now derived
inline from it via a sorry-free `round_intermediate_value` helper
(intermediate-value theorem for validator rounds, by induction on
`step_round_at_most_one`).

This sub-finding was made explicit while integrating Aristotle
project `4f618efb`: an earlier draft used the catch-up form and
Aristotle's bundle proof exposed the gap by needing a separate
`h_lockstep` hypothesis in addition to `SchedulerFairness`.

### F-1b. Lemma 1's strict same-round claim requires more than the catch-up assumption

Paper Lemma 1's actual statement is:

> *"After GST, all honest validators will enter the same round
> within 3Δ."*

The phrase "the same round" is the strict (gap-0) form: at some
post-GST moment, every honest validator is at one specific round.
Mechanizing this against our trace model exposes that **the strict
form is not derivable from the lockstep `SchedulerFairness`
alone**.

**The obstruction.** Our trace executes one step per `step` call,
each step advancing exactly one validator's `currentRound` (or
none, for non-`doAdvance` actions). The trace therefore has a
**gap-1 invariant**:

> *for every reachable state `s`, max − min of the validators'
> `currentRound`s is at most 1.*

But it does **not** have a gap-0 invariant: when one validator
advances via `doAdvance`, its `currentRound` jumps by 1 while
others remain at the previous round, until each takes its own
advance step. Across the 3Δ window post-GST, gap-0 states occur
*transiently* (whenever the system has just finished a "round of
advances"), but gap-1 states also occur (during a round of
advances).

Therefore the strict same-round form would need either:
1. **Atomic round transitions in the model** — `step` advances
   *all* validators simultaneously when `allProposedFor` holds, so
   gap stays at 0. This is a model change.
2. **A gap-0 witness extraction** — find the *first* step in
   `[k₀, k₀ + 3Δ]` at which all honest reach `r + 1`. At that step
   the actor (the last laggard) just advanced from `r` to `r + 1`;
   by the gap-1 invariant on the previous step, no validator was
   at `r + 2`, so all are at exactly `r + 1` at the witness step.
   This requires formalising the gap-1 invariant first
   (~80 lines) plus the witness extraction (~50 lines).

**Our address.** Weaken the bundle conjunct
`BelugaPostGSTLiveness.honest_round_sync` (and the matching
wrapper `lemma1_honest_round_entry`) to the **lockstep-progress
form**:

> *given an honest validator at round `r` at some step `k₀`
> post-GST, there exists a step `k'` within 3Δ at which **all
> honest validators are at round ≥ r + 1**.*

This is exactly the `SchedulerFairness` hypothesis's content
surfaced as a structural property of the trace; the bundle proof
is a one-line `h_fair` call. The deviation from the paper is that
we conclude `≥ r + 1` rather than `= r + 1` (i.e., gap ≤ 1
rather than gap = 0).

**Suggested fix for the paper.** Restate L1 in the
lockstep-progress form. The strict same-round wording is
rhetorical convenience that doesn't reflect what L1's downstream
consumers actually need — see the analysis below.

### F-1b cont. — L1's six paper citations only need the lockstep form

Auditing every cite-site of Lemma 1 in the paper:

1. **§4.2 — setting the per-round timeout `T_rd = 4Δ`.** "*the
   per-round timeout `T_rd`, which is set to 4Δ to ensure all
   honest blocks are received (Lemma 1)*". The justification is
   "round-entry in 3Δ + 1Δ block delivery = 4Δ". Needs only "all
   reach round `≥ r + 1` within 3Δ" — the timeout has to cover
   the slowest validator; whether all are at exactly `r + 1` or
   some at `r + 2` doesn't matter.

2. **§5 Lemma 2 proof** uses L1 to establish "2f+1 honest validators
   have proposed for round `r`". By the protocol's
   propose-before-advance gate (`tryActFor` priority), every
   validator reaching `≥ r + 1` has proposed for `r`. Weaker L1
   suffices.

3. **Happy-case timing analysis (§5)** — same shape as (2): L1
   gives "all at round r within 3Δ"; the downstream needs "all
   created round-r blocks", which follows from the weaker form.

4. **§D.2 Lemma 8 proof** — "*After GST, if an honest validator
   enters a round r, then the honest leader validator (and every
   other honest validator) will **be able to enter** the same
   round r within 3Δ (Lemma 1).*" The phrasing **"be able to
   enter"** is a *reachability* claim, not a simultaneity claim:
   every honest reaches round `r` at some point, which is exactly
   the weaker L1's content (every honest passes through `r` on
   the way to `≥ r + 1`).

5. **§D.2 block-reception bound** — "*By Lemma 1, every honest
   validator can receive 2f+1 honest blocks from round r+1 within
   4Δ*". Same pattern: reach round → propose at that round →
   blocks received. Weaker L1 suffices.

6. **Lemma 4 proof** — "*By Lemma 1, all honest validators enter
   a common round within 3Δ after GST; w.l.o.g. call this round r
   and let `t_r := GST + 3Δ`*". L1 is used as a *naming
   convention* — the round `r` is just "the common round all are
   at". The downstream argument uses "everyone has proposed for
   `r - 1` by `t_r`", which the weaker L1 delivers.

**None of L1's six citations require the strict same-round form.**
The strict wording simplifies the prose ("the same round")
relative to the lockstep-progress form ("at round `≥ r + 1` with
gap ≤ 1") but doesn't pull weight in any downstream argument.
Restating L1 in the lockstep-progress form would (a) make L1
provable from the cited assumptions, (b) match the operational
content the paper's own proofs consume, and (c) reduce the
risk of confusion for readers who try to use L1 in a context
that does need simultaneity (no such context appears in the
present paper, but the strict wording invites mis-application).

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
Lemma 13 (certificate persistence) and Lemma 15 (uniqueness of
certified leader per round).

**Finding.** Each proof relies on a protocol invariant the paper
treats as obvious but doesn't formally state. Mechanizing the proofs
forced four out, all DAG-level facts:

1. **DAG admission well-formedness.** *Every block at a positive
   round has at least `2f + 1` distinct-author parents from the
   immediately preceding round, all themselves in the state.*
2. **Author-round uniqueness.** *Any two blocks in the state with
   the same `(author, round)` are equal.* Stronger than the paper's
   "honest validators don't equivocate" — uniqueness here is total,
   following from the protocol's *propose-op uniqueness* invariant
   (digital signatures + at-most-one-propose-per-round behavior).
3. **No equivocation in parents.** *For any two blocks in the state
   that reference parents with the same `(author', round')`, the
   referenced parents coincide.*
4. **Authors are registered.** *Every block author corresponds to a
   registered validator.*

The proof of L13 (paper §D.3) uses item (1) twice — once at round
`r + 2` for the quorum-intersection step, again at later rounds to
thread the inductive argument — and items (2)–(4) for the
quorum-intersection's "at least one honest validator referenced
both" step. Paper L15 uses the same items (via
`certified_unique`'s quorum-intersection chain).

**Status: ✓ closed for the executable trace.** All four items
are bundled in `Mysticeti.MysticetiSafetyInv`
([`Mysticeti/SafetyInvariant.lean`](../BlockSynchroniser/Mysticeti/SafetyInvariant.lean)),
and `belugaTrace_satisfies_mysticetiSafetyInv` proves the bundle
sorry-free for `belugaTrace system k`:
- item (1) via `belugaTrace_admissionWellFormed` (whose proof in
  [`Beluga/AdmissionInvariant.lean`](../BlockSynchroniser/Beluga/AdmissionInvariant.lean)
  threads a compound `TraceInv` through every `tryActFor` branch);
- items (2) and (3) directly from `BlockInv.uniquePropose`
  (already part of the `BlockInv → AcceptInv → CausallyClosed`
  chain in [`Beluga/Protocol.lean`](../BlockSynchroniser/Beluga/Protocol.lean));
- item (4) via a joint blocks-+-validator-IDs Nat induction
  (Aristotle round `c2ca4a2e`).

The belugaTrace-specialised wrappers
`lemma13_cert_persistence_belugaTrace` and
`lemma15_unique_cert_belugaTrace` consume the bundle, so their
only remaining hypotheses are the genuine BFT side conditions
(`hN`, `h_byz_bound`, `hids`).

**Suggested fix for the paper.** Each of (1)–(4) is candidate
material for a named lemma in §D.3 — they are load-bearing steps
the prose treats as obvious. Naming them would also make L13 and
L15 explicit about which invariants they consume, which is useful
for follow-on protocol designs that vary the parent-selection
rule.

**Note: not in F-5.** Two facts the original entry listed —
"view-traceback" (used in L16) and "decision completeness" (used
in T7) — are *not* DAG invariants; they concern external
`view : ConsensusView` / `order : TransactionOrder` parameters.
Those are tracked under [F-7](#f-7-theorem-7s-prose-proof-slips-a-liveness-step-into-a-safety-claim)
(safety/liveness boundary).

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

## F-3. Surfaced invariants: two honest non-equivocation forms

**Affected statements.** Paper §4.4 uniqueness consequence ("for any
validator and round, at most one block can become certified");
paper §D.3 L13 (certificate persistence).

**Finding.** The paper states honest non-equivocation only within a
single block ("an honest validator's block has at most one parent
per author" or similar in-block phrasings). Two distinct *cross-block*
forms are silently used by paper proofs, neither stated:

- **(a) Cross-block parent-set agreement.** Any two honest-authored
  blocks in the state agree on parents at the same `(author, round)`
  — i.e., if `B_h^r` and `B_h^{r'}` are both authored by the same
  honest validator, then for any `(author', round')` they both
  reference, they reference the *same* parent block.
  Used by `certified_unique` (paper §4.4 uniqueness) in the case
  where the shared honest validator authored two distinct blocks
  each referencing one of two candidate certificates.

- **(b) Block-uniqueness per (author, round).** An honest validator
  authors *at most one* block per `(author, round)` pair — there
  are not two distinct round-`r` blocks both authored by the same
  honest validator.
  Used by paper §D.3 L13's quorum-intersection step: when the
  shared honest validator from the intersection appears as the
  author of both a parent of `B'` and a referencer of `B`, those
  two blocks must be *equal*, not merely agree on parents.

**Suggested fix.** State both forms explicitly alongside the
within-block form. Both follow from the broader principle "honest
validators behave consistently per (author, round)", but the paper's
prose treats them as immediate when they are not.

**Resolution in our formalization.** Form (a) as `NoEquivocationInParents`
(used by `certified_unique`); form (b) as `h_honest_unique` on L13.
Both proved sorry-free under their respective hypotheses.

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

## F-8. Validator-ID assumptions silently used across multiple proofs

**Affected statements.** Paper §D.1.2 round-robin leader schedule
(`leader_of(r) := validators[r mod n]`) and Lemma 10 (round-robin
pigeonhole); paper §4.2 block-digest derivation; paper §2 BFT bound
("at most `f` Byzantine validators").

**Finding.** Three related-but-distinct ID-bound / universe
assumptions surface:

- **(a) Contiguous IDs (stronger).** The round-robin formula
  `r mod n` produces a numeric identifier in `{0, …, n−1}`. For
  "the leader of round `r`" to be a registered validator, the
  validator set must be indexed by exactly that range — IDs are
  `0, 1, …, n−1`. Used by L10 (round-robin pigeonhole).

- **(b) Bounded IDs (weaker).** Block digests are uniquely identified
  by `(round, author)`; for `digest`'s injectivity, validator IDs
  must be bounded (e.g., `vid < n + 1`) so the encoding `r * (n+1)
  + vid` is injective. Used by trace-invariant proofs that rely on
  digest uniqueness (e.g., `causal_history_of_find_none`'s
  `BlockInv` chain, where no-duplicate-digests is load-bearing).

- **(c) BFT bound's universe.** The paper's "at most `f` Byzantine
  validators" is implicitly *a statement about the registered
  validator set* — a list of `2f + 1` arbitrary `ValidatorId`s
  (e.g., the parent-author list of a block in state) is only
  guaranteed to contain ≥ `f + 1` honest validators if it is
  known to be a subset of the registered set. Without that
  qualifier, a list of `f + 1` *unregistered* IDs trivially
  satisfies "all entries are non-honest" (since `isHonest`
  returns `false` for unregistered IDs), violating the bound.

(a) ⇒ (b), so a single statement of (a) discharges both. (c) is
distinct: it doesn't follow from (a)/(b) alone — it is a
universe-of-quantification clarification on the BFT bound itself,
saying that the "at most `f` Byzantine" claim ranges over
*registered* validators, not over the type `ValidatorId`. The
paper takes all three as obvious — none are named.

**Suggested fix.** State explicitly that `system.validators`'s ID
column is `{0, …, n−1}` (perhaps in §2 alongside `n` and `f`), and
in the same paragraph qualify the BFT bound as "for any nodup
list/subset of *registered* validators, at most `f` are Byzantine."
Either is fine; just pin both the universe and the quantification
range.

The (c) sub-finding was surfaced when the formalization tried to
package "at most `f` Byzantine in any author list" as a bundle
conjunct without the registered-list qualifier; Aristotle round
`03f5fe3f` exhibited a concrete refutation (a list of `f+1` copies
of an unregistered ID), confirming that the qualifier is
load-bearing rather than decorative.

This is a low-severity finding compared to F-1 / F-7 — purely
notational hygiene. Recording it for completeness.

---

## F-11. Block-digest determinism is implicit, not stated

**Affected statement.** Paper §2.1 block structure
(`(r, d, author, parents, payload, signature)`) and every uniqueness
argument that follows.

**Finding.** The paper presents `B.d` (block digest) as a primitive
field of the block — alongside `B.r`, `B.author`, etc. But every
uniqueness or no-duplicates argument in the paper silently relies on
the digest being a *function of `(B.r, B.author)`* — i.e.,
"two blocks at the same round by the same author have the same
digest, and conversely two blocks with the same digest agree on
round and author." Without that, `digest` is just a free label and
distinct blocks could share digests (or one block could have multiple
digests across the trace).

This is load-bearing for, among others:

- The Mysticeti-Beluga safety chain (paper §D.3): proofs reason
  about "the certificate set of `B`" via digest membership in
  parent lists.
- The cross-block honest non-equivocation step (F-3): identifying
  "the block authored by validator `v` at round `r`" requires the
  digest to fix the (r, author) pair.
- The L13 quorum-intersection step: equating a parent of `B'` with
  a referencer of `B` via the shared honest validator's digest.

In implementations this comes for free: digests are cryptographic
hashes of the block contents, which include `(r, author)`. But a
*formal* statement of the protocol that doesn't make digests a
function of contents is missing this load-bearing fact.

**Suggested fix.** Either:

1. Define `B.d` as a function of `(B.r, B.author, ...)` rather than
   a primitive field — the cleanest restatement.
2. State block-digest determinism as a named protocol property
   alongside Definition 1.

**Resolution in our formalization.** The trace-invariant
`BlockInv` (in the `causal_history_of_find_none` chain) carries
`B.d = digest system B.r B.author` as an invariant of the executable
trace, and `digest_injective` is derived from it (under `ValidIds`
— see F-8). So the formalization works, but only because we surfaced
this as an invariant; the paper's statement-level treatment elides it.

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
