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

## What the paper assumes, what we prove, and what we leave assumed

The §5 mechanization concludes with a single Prop bundle,
`BelugaWithPullFairness`, that names every assumption the paper
relies on but does not always state. The bundle has seven fields,
each corresponding to a single sentence one could add to the paper:

| Field                | Paper reference / paper-language statement |
|----------------------|--------------------------------------------|
| `timeMonotone`       | the global wall clock is non-decreasing along the trace |
| `timeUnbounded`      | the wall clock eventually passes any time bound |
| `networkDelivery`    | §2 — every push message between honest validators is delivered within `Δ` after GST |
| `actionScheduling`   | §4.2 — every honest validator advances rounds within `Δ` after GST (per-round timeout `T_rd = 4Δ`) |
| `boundedRoundSpread` | §4.2 — at any post-GST step, the rounds of any two honest validators differ by at most one |
| `acceptScheduling`   | §4.2 — when an honest validator has an acceptable in-pool block, it accepts within `Δ` after GST |
| `inPoolDelivery`     | §4.3 — every block in the global pool is eventually known to every honest validator (push channel of §2 ∪ pull mechanism of §4.3) |

Under exactly these seven assumptions, the §5 corollary
`beluga_isBlockSynchronizer` derives all four block-synchronizer
properties — T1 (Block Availability), T2 (Causal Availability), T3
(Round Progression), T4 (Round Termination) — together with L1
(round entry within `3Δ`) and L2 (round-to-round latency `≤ 3Δ`).
**Both `EventualCausalAcceptance` and `EventualRoundAcceptance`,
which earlier had to be taken as axioms, are now derived theorems.**

What the paper assumes implicitly that we surface here:

- The **per-action liveness rates** of §4.2 — `actionScheduling`,
  `acceptScheduling` — are what the paper writes as "honest
  validators run the protocol" and uses to derive the `3Δ` round
  bound. The paper does not state them as separate primitives.
- The **§4.3 pull mechanism's liveness conclusion** — that any
  in-pool block is eventually known to every honest validator — is
  the load-bearing fact used by T2's prose proof. The paper sketches
  the mechanism but never names the conclusion. We give it as
  `inPoolDelivery`. See "Why item 6 is taken as an assumption"
  below.
- The **gap-1 round-spread invariant** — `boundedRoundSpread` — is
  what the paper's §5 prose calls "all honest validators are at
  comparable rounds". The paper's L1 phrasing ("the same round")
  suggests gap-0; our trace model surfaces gap-1 transient states
  unavoidable when one validator advances at a time. See F-1.

What we leave as assumptions (do not derive from anything else):

- The first six fields of `BelugaWithPullFairness` (clock,
  push delivery, round-advance, protocol synchronization,
  accept-action liveness) are paper-stated post-GST liveness
  primitives. They cannot be derived without modelling individual
  messages and per-validator clocks at finer granularity.
- The seventh field, `inPoolDelivery`, is also taken as an
  assumption in the current formalization, but for a different
  reason. See immediately below.

### Why item 6 (`inPoolDelivery`) is taken as an assumption

In the **paper's level of abstraction**, where each validator has
its own independent DAG view, item 6 is the §4.3 conclusion
delivered by the pull mechanism. The pull mechanism's correctness
rests on `ImPoA` and the standard quorum-intersection argument:
when an honest validator `v` issues a pull for a block `B` that
it has not received via push, the f+1 in-pool blocks referencing
`B` guarantee that at least one honest validator already holds
`B` and will respond. Without `ImPoA`, item 6 would not follow
from the §2 push primitive alone.

In **our trace model**, the block pool is shared (`s.base.blocks`
is a single list, not per-validator). Combined with the atomic
§4.3 primitives we have stated and proved sound on the trace —
`PullRequestDelivery` (post-GST honest pull requests reach honest
responders' inboxes within `Δ`) and `PullResponseScheduling`
(honest responder with non-empty `pullInbox` drains the first
request within `Δ`) — plus `NetworkDeliveryWithPull` for the
push channel, item 6 is *in principle derivable*. The chain is

> `pullCandidate` identifies the missing block at vid → `pullStepOne`'s
> issue branch fires (vid emits a pull request via `doPullRequest`)
> → `PullRequestDelivery` lands the request in some honest
> responder's inbox → `PullResponseScheduling` fires `doPullResponse`
> → `doPullResponse` schedules a `block_propose` `DeliveryEvent`
> → `deliverPending` lands the op in vid's inbox.

What it would take to discharge item 6 from the more atomic
primitives is a non-trivial liveness proof: each step in this
chain is a separate post-GST `Δ`-bounded liveness step that has
to be threaded through the trace's evolution. The proof would
amount to ~200–300 lines of structural tactic work, comparable in
size to the Phase 11 (`network_eventualCausalAcceptance`) proof
that *consumes* item 6. We therefore state item 6 as a primitive
in the bundle, paralleling how the paper presents §4.3's
conclusion as the design intent of the pull mechanism rather than
as a derived fact.

The bottom line: in our trace model, item 6 is structurally
derivable from `PullRequestDelivery` + `PullResponseScheduling`
+ push delivery + the pull driver code — but the derivation is
itself a substantial proof we have not undertaken. It is taken as
a primitive of the bundle, with the understanding that any future
work that wants to remove it from the assumption list has a clear
target.

What we prove from `BelugaWithPullFairness` alone:

- L1 (`lemma1_honest_round_entry`), L2 (`lemma2_round_latency`).
- T1 (`network_theorem1_block_availability_withPull`),
  T2 (`network_theorem2_causal_availability_withPull`),
  T3 (`network_theorem3_round_progression_withPull`),
  T4 (`network_theorem4_round_termination_proved`).
- The `BlockSynchronizer` corollary (`beluga_isBlockSynchronizer`).
- Internally: `EventualCausalAcceptance` and
  `EventualRoundAcceptance` as theorems
  (`network_eventualCausalAcceptance`,
  `network_eventualRoundAcceptance`).

## Summary of findings

Findings are grouped by status. Within each group, listed by severity.

**Status legend:**

- ✅ **Resolved** — hypothesis explicit / invariant named **and**
  proofs go through (or, for documentation findings, the choice
  has been settled).
- ⚠️ **Open** — not addressed yet.

### ⚠️ Open

| ID | Severity | Category | Affected | Headline |
|---|---|---|---|---|
| **F-1b** | High | Statement-level wording | §5 L1 | Paper L1 reads "all honest validators enter the same round within 3Δ" (the strict gap-0 form). Our model exposes a gap-1 invariant: when one validator advances, others are transiently one behind. The strict same-round form is therefore not provable from the paper's stated assumptions. The lockstep-progress form ("all reach round `≥ r + 1` within 3Δ") is what L1's downstream consumers actually need. |
| **F-7** | High | Missing assumption (safety/liveness boundary) | §D.3 T7 | T7's prose proof equates "consistent views" (L16) with "identical views" (needs liveness — F-7a) and treats `order` as separable from `view` (it isn't — F-7b). Two non-paper ingredients hidden in one short paragraph. |

### ✅ Resolved

| ID | Severity | Category | Affected | Headline | Our address |
|---|---|---|---|---|---|
| **F-1** | High | Missing assumptions surfaced as a bundle | §5 L1, L2 (and downstream §5 T1–T4) | Paper's §5 proofs silently use a *scheduler-fairness* step ("validators act promptly") that is not stated anywhere. The paper also leaves the §4.3 pull mechanism's liveness conclusion implicit. | The seven paper-stated and paper-implicit assumptions of §2 + §4.2 + §4.3 are bundled in `BelugaWithPullFairness` (`Beluga/Theorems.lean`); the §5 corollary `beluga_isBlockSynchronizer` consumes the bundle once. |
| **F-1a** | High | Sub-finding of F-1 | §5 L2 derivation | The round-level shadow of "validators act promptly" actually used by L2 is the **lockstep** form (`≥ r + 1` within `3Δ`), not the catch-up form (`≥ r` within `3Δ`). The catch-up form is too weak to give L2's "round `r + 1` within `3Δ`" conclusion. | `actionScheduling` (in the bundle) is the lockstep-shaped primitive. `lemma2_round_latency` is derived from `lemma1_honest_round_entry` + the round-level intermediate-value theorem `network_round_intermediate_valueWithPull`. |
| **F-1c** | High | Pull-mechanism modelling | §4.3 pull mechanism | An earlier mechanization left the pull mechanism implicit and required a `NetworkBelugaCoherence` axiom to bridge the network model and the simpler abstraction §5 prose uses. | The pull mechanism is now modelled explicitly: `PullRequest` events, `pullRequestsInflight` / `pullRequestsInbox` queues on `NetworkState`, `doPullRequest` / `doPullResponse` actions, the `pullStep` driver, and the `networkStepWithPull` / `networkTraceWithPull` step/trace functions. The paper §4.3 + §4.2 per-action liveness primitives `AcceptScheduling`, `PullRequestDelivery`, `PullResponseScheduling`, and the consolidated `NetworkInPoolDeliveryWithPull` are stated against this trace. `EventualCausalAcceptance` and `EventualRoundAcceptance` are now derived theorems; `NetworkBelugaCoherence` is deleted. |
| **F-2** | Medium | Scope-pinning | §2 (model), used throughout | The `\|A∩B\| ≥ f+1` bound for two `(2f+1)`-quorums only holds at `n = 3f+1` exactly; the paper writes `f < n/3` but uses fixed `2f+1` quorums uniformly. | `n = 3 * f + 1` explicit hypothesis on `quorumIntersection`, `certified_unique`, `lemma15_unique_cert`, `lemma10_round_robin_pigeonhole`; all proved. |
| **F-3** | Medium | Surfaced invariant | §4.4 (uniqueness), §D.3 L13 | Paper's "honest validators don't equivocate" is stated within-block; uniqueness proofs need both the cross-block parent-set agreement form and the block-uniqueness form (an honest validator authors at most one block per `(author, round)` pair). | Form (a) as `NoEquivocationInParents`; form (b) as `h_honest_unique` on L13. Both proved sorry-free; for `belugaTrace` both are derived sorry-free from `BlockInv.uniquePropose` via `Mysticeti.MysticetiSafetyInv`. |
| **F-4** | Low | Editorial — naming an invocation | §C.2 L4, L5 | Proofs of L4/L5 invoke Assumption 1 (latency triangle) implicitly to derive per-round Δ advancement. | `LatencyTriangle` explicit hypothesis on L4 and L5; both proved sorry-free. |
| **F-5** | Medium | Surfaced invariant | §D.3 L13 + L15 | Each proof relies on protocol-invariant DAG facts the paper takes as obvious — DAG admission well-formedness, author-round uniqueness, no-equivocation in parents, authors-are-registered. None are stated as lemmas. | The four conjuncts are bundled in `Mysticeti.MysticetiSafetyInv` and `belugaTrace_satisfies_mysticetiSafetyInv` proves the bundle sorry-free. |
| **F-6** | Low | Editorial | §4.2 prose vs Figure 8 | Reputation-update trigger is `r−1` in the prose and `r−2` in the pseudocode (off-by-one due to round-increment timing). | Followed the prose (`r-1`); flagged in `formalization.md`'s "Notes on paper consistency" section. |
| **F-8** | Low | Notational hygiene | §D.1.2 (round-robin), §D.3 L10, §4.2 (digest), §2 (BFT bound) | Three related ID-bound assumptions are silent: `r mod n` round-robin presumes IDs `{0, …, n−1}`; digest injectivity presumes IDs bounded by `n+1`; the "at most `f` Byzantine" bound is implicitly *over the registered validator set*. | Form (a) as `h_ids` on L10; form (b) as `ValidIds` in the trace-invariant chain; form (c) surfaced by the registered-list hypothesis in the Mysticeti liveness layer. |
| **F-11** | Medium | Notation / definition | §2.1 block structure | Block digest `B.d` is treated as a primitive field, but every uniqueness argument silently relies on it being a function of `(B.r, B.author)`. | `BlockInv` carries `B.d = digest system B.r B.author` as a trace invariant; `digest_injective` derived. |
| **F-12** | Low | §5 proof simplification | §5 T1, T2 | The paper's §5 proofs of T1 and T2 lean on the ImPoA / pull-protocol mechanism, but with action-priority (accept before store before round-advance, all above propose) the "eventually" claims of T1 and T2 collapse to single-step structural facts. | T1 and T2 mechanized without ImPoA reasoning; alternative proof sketches in [`paper-additions-stage2.md`](paper-additions-stage2.md). |
| **F-13** | Low | Definitional ambiguity | §4 prose vs. Figure 8 | Paper Figure 8 emits both `block_accept` and `block_store` in a single procedure step; §4 prose treats them as separately observed at different consumers. | Mechanized as separate actions with priority ordering; T1's proof uses the action-priority argument (matches F-12). |

Each entry has a stable identifier (`F-N`) so we can refer to them
across documents.

---

## F-1. Missing assumptions: §5 silently relies on per-action scheduling and pull-channel liveness

**Affected statements.** Paper §5, Lemma 1 ("after GST, all honest
validators will enter the same round within `3Δ`"), Lemma 2
("after GST, if an honest validator enters round `r` at time `t_r`
and all honest validators have created and disseminated their
round `r` blocks by time `t_r`, then all honest validators will be
able to enter round `r+1` by time `t_r + 3Δ`"), and theorems
T1–T4.

**Finding.** None of L1, L2, T1–T4 follows from the paper's
explicit assumptions alone. The prose proofs use:

1. An implicit **scheduler-fairness** step — "the validator
   processes the block / advances its round / executes its local
   action *promptly*" — that is not stated anywhere. Without it,
   no time bound on round entry can be derived.
2. An implicit **pull-channel liveness** conclusion — "the
   validator eventually pulls the missing block" — used by T2's
   causal-availability argument and T4's round-termination
   argument. The §4.3 pull mechanism is described, but the
   liveness conclusion that any in-pool block reaches every
   honest validator is left informal.

**Counterexample for (1).** Take `n = 4`, `f = 1`, four honest
validators, GST = 0, Δ = 10. Suppose post-GST the network behaves
as the paper assumes (every honest-to-honest message delivered
within Δ). However, the local processing schedule is asymmetric:
validator `v_0` runs continuously and reaches round 1 by time 5,
while `v_1, v_2, v_3` are not given CPU time during the interval
`[0, 30]` and so take no local action during that window. At time
`30 = GST + 3Δ`, `v_0` is in round 1 and `v_1, v_2, v_3` are still
in round 0 — Lemma 1 is violated.

**Where the prose proof hides (1).** Sentences such as

> "By Assumption 1 (latency triangle), if `v_i` is honest and sends
> `B_i^{r-1}` to `v_j`, then `v_j` receives `B_i^{r-1}` directly
> before receiving it via an intermediate validator … hence `v_j`
> accepts `B_i^{r-1}` …"

silently equate "`v_j` *receives* the block within Δ" (true under
Assumption 1) with "`v_j` *processes* the block within Δ" (requires
scheduler fairness). The same equivocation appears in:

> "they can accept these blocks via the pull protocol within `2Δ`."

**Where the prose proof hides (2).** T2's argument that an honest
validator "eventually pulls" any unaccepted causal ancestor. The
pull mechanism is described in §4.3, but the conclusion that the
mechanism *always succeeds* when the block is in the pool is never
named and never derived from atomic primitives.

**Suggested fix.** Make both ingredients explicit. The simplest
way is to restate the §5 assumptions as the seven items of
`BelugaWithPullFairness`. In paper-friendly language:

> **Assumption 2 (per-action liveness).** Post-GST, whenever an
> honest validator `v` is in a state where the protocol of §4.2
> enables a local action (propose, accept, store, or advance), `v`
> performs that action within `Δ` of becoming enabled.

> **Assumption 3 (pull-channel liveness, §4.3).** Post-GST, every
> block in the global pool is eventually known to every honest
> validator — either via the §2 push channel (for honest authors)
> or via the §4.3 pull mechanism (otherwise).

These are the conclusions the paper's §5 prose actually consumes;
making them explicit clarifies which §5 facts are *protocol*
properties (T1–T4 with the action-priority argument) and which are
*liveness* properties of the network model.

**Detailed write-up.** See
[paper-feedback-l1-l2-fairness.md](paper-feedback-l1-l2-fairness.md)
for the (1)-half discussion, formal counterexample trace, and
discussion of where the prose silently relies on the assumption.

**Follow-up: ImPoA does not substitute for scheduler fairness.**
A natural question is whether ImPoA (paper §4.3) — given how
prominently it features in the §5 prose proofs — somehow replaces
the missing fairness assumption. It does not: ImPoA is a passive
structural property of the DAG (a block is implicitly available
*iff* `f + 1` subsequent blocks reference it), and is a
correctness/bandwidth mechanism for *acceptance*, not a liveness
trigger for *round advance*. The paper's actual liveness mechanism
is the per-round timeout `T_rd = 4Δ` (paper §4.2), which fires
unconditionally on a validator's local clock. Combined with
`Δ`-delivery + push protocol + ImPoA, this yields paper L1's `3Δ`
bound. See
[paper-feedback-impoa-vs-fairness.md](paper-feedback-impoa-vs-fairness.md)
for the full analysis.

### F-1a. Round-level corollary needed in *lockstep* form (`≥ r + 1`)

When discharging the per-action liveness assumption to a
round-level fact, the *catch-up* form

> post-GST, when some honest validator reaches round `r`, every
> honest validator reaches round `r` within `3Δ`

is too weak to derive Lemma 2 (which concludes "round `r + 1`
within `3Δ`"). The form actually needed is the **lockstep**
variant

> post-GST, when some honest validator reaches round `r`, every
> honest validator reaches round `r + 1` within `3Δ`,

which corresponds to the per-action assumption being applied
through *one full §4 round transition* (advance + propose + accept
+ advance) rather than just enough actions to catch up. The `+ 1`
captures the combined effect of the §4 `allProposedFor` gate and
per-action scheduler fairness: in `3Δ` not only does everyone
catch up, but the leader also advances.

**Status: ✅ Resolved.** The bundle's `actionScheduling` field is
the lockstep-shaped primitive, and L2 (`lemma2_round_latency`) is
derived from L1 (`lemma1_honest_round_entry`) via the round-level
intermediate-value theorem.

### F-1b. Lemma 1's strict same-round claim requires more than the catch-up assumption

Paper Lemma 1's actual statement is:

> *"After GST, all honest validators will enter the same round
> within 3Δ."*

The phrase "the same round" is the strict (gap-0) form: at some
post-GST moment, every honest validator is at one specific round.
Mechanizing this against our trace model exposes that **the
strict form is not derivable from the bundle's primitives alone**.

**The obstruction.** The trace executes one step per `step` call,
each step advancing exactly one validator's `currentRound` (or
none, for non-`doAdvance` actions). The trace therefore has a
**gap-1 invariant** (`boundedRoundSpread` in the bundle):

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
   *all* validators simultaneously when `allProposedFor` holds,
   so gap stays at 0. This is a model change.
2. **A gap-0 witness extraction** — find the *first* step in
   `[k₀, k₀ + 3Δ]` at which all honest reach `r + 1`. At that
   step the actor (the last laggard) just advanced from `r` to
   `r + 1`; by the gap-1 invariant on the previous step, no
   validator was at `r + 2`, so all are at exactly `r + 1` at the
   witness step. This requires further structural work.

**Our address.** The §5 wrapper `lemma1_honest_round_entry`
states the **lockstep-progress form**:

> *given an honest validator at round `r` at some step `k₀`
> post-GST, there exists a step `k'` within 3Δ at which **all
> honest validators are at round ≥ r + 1**.*

This is exactly what the action-scheduling assumption surfaces as
a structural property of the trace; the wrapper's proof is a
one-line invocation. The deviation from the paper is that we
conclude `≥ r + 1` rather than `= r + 1` (i.e., gap ≤ 1 rather
than gap = 0).

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
content the paper's own proofs consume, and (c) reduce the risk
of confusion for readers who try to use L1 in a context that does
need simultaneity (no such context appears in the present paper,
but the strict wording invites mis-application).

### F-1c. §4.3 pull mechanism and the eventual-acceptance conclusions

**Earlier state.** A previous mechanization left the §4.3 pull
mechanism implicit and required a `NetworkBelugaCoherence` axiom
to bridge the network model and the simpler abstraction §5 prose
uses. The two §5-load-bearing eventual conclusions —
`EventualCausalAcceptance` (T2) and `EventualRoundAcceptance`
(T4) — were taken as axioms.

**Status: ✅ Resolved.** The pull mechanism is now modelled
explicitly:

- `PullRequest` events on `NetworkState`, with
  `pullRequestsInflight` and `pullRequestsInbox` queues.
- The `doPullRequest` and `doPullResponse` actions, the
  `pullStepOne` per-validator driver, and the `pullStep` system
  fold.
- The `networkStepWithPull` and `networkTraceWithPull` functions
  layering pull on top of the §4.2 push step.

The paper §4.3 + §4.2 per-action liveness primitives —
`AcceptScheduling` (paper §4.2's accept-action liveness),
`PullRequestDelivery` (the pull-channel `Δ`-delivery), and
`PullResponseScheduling` (the pull-response action) — are stated
against this trace. The consolidated guarantee `inPoolDelivery`
(`NetworkInPoolDeliveryWithPull`) captures the §4.3 conclusion
that every in-pool block is eventually known to every honest
validator.

`EventualCausalAcceptance` and `EventualRoundAcceptance` are now
**derived theorems** (`network_eventualCausalAcceptance`,
`network_eventualRoundAcceptance`); the §5 corollary needs no
`Eventual*` axioms. The `NetworkBelugaCoherence` axiom is deleted.

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
differ on which leader blocks they have already decided (one
ahead, the other still `Undecided` on slots the leader has
committed). That difference is a liveness phenomenon, not a
safety one.

To bridge "consistent views" to "identical views" you need:

> *(decision completeness)* For any two honest validators `v_1,
> v_2` and any digest `d`: `v_1` has decided `d` iff `v_2` has
> decided `d`.

Decision completeness is **not** a safety property. It is the
*liveness* claim "all honest validators eventually decide the
same slots", which the protocol satisfies after GST + bounded
delay, but only as a consequence of the consensus *liveness*
theorems (Theorem 6 and the lemmas of §D.2).

### F-7b. "Transaction ordering respects view equality" hides a definition

The paper writes as if `order(v)` is an independent observable
that "respects view equality". In a literal model where `view`
and `order` are introduced as separate entities, you would need a
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
   as a named premise and cite Theorem 6 / §D.2 for its discharge.

3. **Make the order-from-view definition explicit** in §D.3 (one
   sentence: "`order(v)` is the canonical traversal of the causal
   history of `v`'s committed leader blocks") so that F-7b
   becomes a non-issue.

Most BFT papers adopt one of these stances implicitly. We suggest
being explicit about which.

---

## F-2. Scope-pinning: quorum-intersection bound at `n = 3f + 1`

**Affected statement.** Implicit in §2 (BFT model: `f < n/3`) and
used throughout: any two `(2f+1)`-quorums intersect in at least
`f + 1` validators (and hence at least one honest validator if
`|A ∩ B| ≥ f + 1`).

**Finding.** The intersection bound `|A ∩ B| ≥ f + 1` follows
from inclusion-exclusion only when `n = 3f + 1` exactly:

`|A ∩ B| ≥ |A| + |B| − n = (2f+1) + (2f+1) − (3f+1) = f + 1.`

For `n > 3f + 1` (still satisfying `f < n/3`) the bound becomes
`|A ∩ B| ≥ 4f + 2 − n`, which can be smaller than `f + 1`. The
paper writes `f < n/3` but uses `2f + 1` quorums uniformly,
implicitly fixing the quorum size rather than scaling it with
`n`.

**Suggested fix.** Either (a) pin `n = 3f + 1` explicitly in the
model (matches the paper's worked examples and is unambiguous), or
(b) replace `2f + 1` with `n − f` in the protocol description so
the intersection bound holds for all `n ≥ 3f + 1`.

We chose option (a) for the formalization since it matches the
paper's intent without changing protocol numbers.

---

## F-3. Surfaced invariants: two honest non-equivocation forms

**Affected statements.** Paper §4.4 uniqueness consequence ("for
any validator and round, at most one block can become certified");
paper §D.3 L13 (certificate persistence).

**Finding.** The paper states honest non-equivocation only within
a single block ("an honest validator's block has at most one
parent per author" or similar in-block phrasings). Two distinct
*cross-block* forms are silently used by paper proofs, neither
stated:

- **(a) Cross-block parent-set agreement.** Any two honest-authored
  blocks in the state agree on parents at the same `(author,
  round)` — i.e., if `B_h^r` and `B_h^{r'}` are both authored by
  the same honest validator, then for any `(author', round')`
  they both reference, they reference the *same* parent block.
  Used by `certified_unique` (paper §4.4 uniqueness) in the case
  where the shared honest validator authored two distinct blocks
  each referencing one of two candidate certificates.

- **(b) Block-uniqueness per (author, round).** An honest
  validator authors *at most one* block per `(author, round)`
  pair — there are not two distinct round-`r` blocks both
  authored by the same honest validator.
  Used by paper §D.3 L13's quorum-intersection step: when the
  shared honest validator from the intersection appears as the
  author of both a parent of `B'` and a referencer of `B`, those
  two blocks must be *equal*, not merely agree on parents.

**Suggested fix.** State both forms explicitly alongside the
within-block form. Both follow from the broader principle "honest
validators behave consistently per (author, round)", but the
paper's prose treats them as immediate when they are not.

---

## F-4. Surfaced invariant: implicit use of Assumption 1 in L4 & L5

**Affected statements.** Paper Appendix C.2, Lemma 4 (round
latency `Δ` when honest reputations dominate) and Lemma 5
(deterministic part — round latency `2Δ` or some malicious
validator is blamed).

**Finding.** The proofs of L4 and L5 invoke Assumption 1 (latency
triangle) implicitly, deriving the per-round `Δ` advancement
bound from "post-GST, the slowest honest validator's round
advances within `Δ`". This is the conclusion of Assumption 1
specialised to round advancement, but the proof prose treats it
as immediate.

**Suggested fix.** Cite Assumption 1 explicitly in the proofs of
L4 and L5, or state a derived corollary

> *Post-GST, if all honest validators are at round `r`, they all
> reach round `r + 1` within `Δ`,*

as a named consequence of Assumption 1 used by L4, L5.

This is a minor expositional issue; the math is correct, the
invocation just isn't named.

---

## F-5. Surfaced invariants: protocol facts assumed in safety proofs

**Affected statements.** Paper §D.3 (Mysticeti-Beluga safety),
Lemma 13 (certificate persistence) and Lemma 15 (uniqueness of
certified leader per round).

**Finding.** Each proof relies on a protocol invariant the paper
treats as obvious but doesn't formally state. Mechanizing the
proofs forced four out, all DAG-level facts:

1. **DAG admission well-formedness.** *Every block at a positive
   round has at least `2f + 1` distinct-author parents from the
   immediately preceding round, all themselves in the state.*
2. **Author-round uniqueness.** *Any two blocks in the state
   with the same `(author, round)` are equal.*
3. **No equivocation in parents.** *For any two blocks in the
   state that reference parents with the same `(author', round')`,
   the referenced parents coincide.*
4. **Authors are registered.** *Every block author corresponds to
   a registered validator.*

**Suggested fix for the paper.** Each of (1)–(4) is candidate
material for a named lemma in §D.3 — they are load-bearing steps
the prose treats as obvious. Naming them would also make L13 and
L15 explicit about which invariants they consume, which is useful
for follow-on protocol designs that vary the parent-selection
rule.

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

---

## F-8. Validator-ID assumptions silently used across multiple proofs

**Affected statements.** Paper §D.1.2 round-robin leader schedule
(`leader_of(r) := validators[r mod n]`) and Lemma 10 (round-robin
pigeonhole); paper §4.2 block-digest derivation; paper §2 BFT
bound ("at most `f` Byzantine validators").

**Finding.** Three related-but-distinct ID-bound / universe
assumptions surface:

- **(a) Contiguous IDs (stronger).** The round-robin formula
  `r mod n` produces a numeric identifier in `{0, …, n−1}`. For
  "the leader of round `r`" to be a registered validator, the
  validator set must be indexed by exactly that range — IDs are
  `0, 1, …, n−1`. Used by L10.
- **(b) Bounded IDs (weaker).** Block digests are uniquely
  identified by `(round, author)`; for digest injectivity,
  validator IDs must be bounded.
- **(c) BFT bound's universe.** The paper's "at most `f`
  Byzantine validators" is implicitly *a statement about the
  registered validator set* — a list of `2f + 1` arbitrary
  `ValidatorId`s is only guaranteed to contain ≥ `f + 1` honest
  validators if it is known to be a subset of the registered set.

(a) ⇒ (b), so a single statement of (a) discharges both. (c) is
distinct: it doesn't follow from (a)/(b) alone — it is a
universe-of-quantification clarification on the BFT bound itself,
saying that the "at most `f` Byzantine" claim ranges over
*registered* validators, not over the type `ValidatorId`. The
paper takes all three as obvious — none are named.

**Suggested fix.** State explicitly that `system.validators`'s ID
column is `{0, …, n−1}` (perhaps in §2 alongside `n` and `f`),
and in the same paragraph qualify the BFT bound as "for any nodup
list/subset of *registered* validators, at most `f` are
Byzantine."

---

## F-11. Block-digest determinism is implicit, not stated

**Affected statement.** Paper §2.1 block structure
(`(r, d, author, parents, payload, signature)`) and every
uniqueness argument that follows.

**Finding.** The paper presents `B.d` (block digest) as a
primitive field of the block — alongside `B.r`, `B.author`, etc.
But every uniqueness or no-duplicates argument in the paper
silently relies on the digest being a *function of `(B.r,
B.author)`* — i.e., "two blocks at the same round by the same
author have the same digest, and conversely two blocks with the
same digest agree on round and author." Without that, `digest`
is just a free label and distinct blocks could share digests (or
one block could have multiple digests across the trace).

This is load-bearing for, among others:

- The Mysticeti-Beluga safety chain (paper §D.3): proofs reason
  about "the certificate set of `B`" via digest membership in
  parent lists.
- The cross-block honest non-equivocation step (F-3).
- The L13 quorum-intersection step.

In implementations this comes for free: digests are cryptographic
hashes of the block contents, which include `(r, author)`. But a
*formal* statement of the protocol that doesn't make digests a
function of contents is missing this load-bearing fact.

**Suggested fix.** Either:

1. Define `B.d` as a function of `(B.r, B.author, ...)` rather
   than a primitive field — the cleanest restatement.
2. State block-digest determinism as a named protocol property
   alongside Definition 1.

---

## F-12. §5 proof strategies: action-priority obviates ImPoA-based reasoning

The paper's §5 proofs of T1 (block availability) and T2 (causal
availability) lean on the ImPoA / pull-protocol mechanism — "the
parent blocks are referenced by f+1 subsequent blocks → at least
one honest stored them → pull → eventually accept". Our
mechanized proofs of T1 and T2 do not need ImPoA at all.

The reason is structural: when accept and store actions are
priority-ordered (accept before store before round-advance, all
above propose), the "eventually" claims of T1 and T2 collapse to
single-step structural facts:

- **T1** holds because store sits strictly above round-advance in
  the action priority. At the next round-advance step, every
  accepted-and-still-in-pool digest must already be stored
  (otherwise the higher-priority store action would have fired).
- **T2** holds because the accept rule itself requires
  parent-acceptance before accepting a block. The accepted-digest
  set is closed under causal-ancestor lookup at every step — no
  eventual quantifier needed.

The ImPoA-based reasoning in §4.3 is still required for the
*runtime* of the protocol (it is what enables a validator to
participate without having directly received every block); but it
is not load-bearing for the *correctness* properties T1, T2. A
reader trying to formalize from §5 may waste effort tracing the
ImPoA argument through the T1 and T2 proofs.

**Suggested paper change.** State T1 and T2 with the simpler
action-priority argument (rewritten proof sketches in
[`paper-additions-stage2.md`](paper-additions-stage2.md));
preserve the ImPoA discussion in §4.3 as the *implementation*
mechanism it is, decoupled from the safety/liveness proofs of §5.

---

## F-13. Accept-store atomicity: paper Figure 8 vs. action-split

Paper Figure 8 (Appendix E) line 13 has `create_new_block` emitting
both `block_accept_i` and `block_store_i` for the new block in a
single procedure step. The §5 prose proofs implicitly assume this
atomicity (e.g., T1's proof says "v_i must have stored B" as a
direct consequence of having accepted B).

If accept and store are instead taken as two distinct outputs
(which the paper's §4 prose does, treating them as separately
observed at different consumers — §4.4 "consensus" reads
`block_accept`, "execution" reads `block_store`), T1's conclusion
is no longer trivially true at the moment of acceptance:
"eventually stores" requires at least one further protocol step.

**Suggested paper change.** Either (a) make the atomicity
explicit by collapsing accept and store into a single
`block_accept_and_store` action in Figure 8, after which T1's
conclusion holds at the step of acceptance and T1's proof is
one sentence; or (b) split accept and store as separate actions
and use the action-priority argument of F-12 for T1 (this matches
our mechanization).

The current paper presentation is mildly ambiguous: §4 prose
treats accept and store as conceptually distinct, while Figure 8
glues them into one step. This finding is invisible to a reader
who does not try to derive T1 mechanically; the paper's prose
proofs read fine without it.

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
(like F-1 has), open a new `docs/round-01/paper-feedback-<topic>.md` and
link it from the entry here.
