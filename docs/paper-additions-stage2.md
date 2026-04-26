# Stage 2 — Paper-side notes from the mechanization

> Companion to [`paper-additions-stage1.md`](paper-additions-stage1.md).
> Stage 1 covers items whose Lean proofs were fully closed at its
> writing. Stage 2 records items surfaced *after* Stage 1, again
> only for items where the mechanization has settled enough to
> warrant a paper-author-facing recommendation. The companion
> [`formalization.md`](../formalization.md) remains the per-item
> proof-status table.

This stage adds one paper-author-facing item beyond Stage 1: a
clarification of paper Lemma 1's statement, surfaced while
mechanizing the Beluga §5 bundle.

A purely formalization-side hygiene point also arose during this
stage (the BFT bound's universe of quantification — finding
**F-8(c)** in
[`mechanization-findings.md`](mechanization-findings.md)). It is
*not* listed here because, from a paper reader's perspective, the
issue is invisible: the paper's prose uses "validators" to mean
the registered set throughout, and the literal misreading only
arises when one tries to formalize against an unrestricted
`ValidatorId` type. The paper's authors don't need to act on it
unless they want maximal cross-formalization-friendliness; if so,
the recommended one-sentence change is recorded in the F-8 entry.

---

## 1. §5 — Lemma 1 says "the same round" but the proof's content is "≥ r + 1"

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

### Audit: none of L1's six citations need the strict form

We checked every site in the paper that cites Lemma 1:

| Cite | What it needs |
|---|---|
| §4.2 — timeout `T_rd = 4Δ` setting | "all reach round `≥ r + 1` in 3Δ" (slowest validator covers the timeout) |
| §5 L2 proof — "2f+1 honest proposed for r" | "all reach `≥ r + 1`" + protocol's propose-before-advance gate |
| Happy-case timing analysis (§5) | same as L2 |
| §D.2 L8 proof — "honest leader **able to enter** round r" | reachability claim — explicit phrasing in the proof |
| §D.2 block-reception bound | reach round → propose at that round → blocks received |
| Lemma 4 proof — "call the common round r" | naming convention; downstream uses "everyone proposed for r-1" |

**None requires gap-0 simultaneity.** The strict same-round
phrasing is rhetorical — it reads cleanly but doesn't pull weight
in any downstream argument. Restating L1 in the lockstep-progress
form would make L1 *both* provable from the cited assumptions
*and* a tighter match to the paper's actual usage; the existing
prose in §5 / §D.2 would not need to change.

---

## 2. §5 proof rewrites: matching the mechanized argument

Our Lean proofs for T1, T3, T4 and L1, L2 were closed *without*
using ImPoA's f+1-references mechanism or the full pull protocol
machinery the paper's §5 prose proofs invoke. The Lean argument
relies on the **action-priority** structure of `tryActFor`
(propose → accept → store → advance), the **lockstep `SchedulerFairness`**
assumption (F-1a), and a small set of trace invariants.

This section gives English rewrites for each §5 proof that
faithfully captures the mechanized argument, in roughly the same
length as the existing proof sketches. The paper's existing prose
*could* be replaced wholesale or kept alongside as a higher-level
narrative; the rewrites below are the load-bearing arguments,
suitable for a formalist reader.

### 2.1 Lemma 1 (rewrite — see also F-1b for the statement weakening)

**Lemma 1 (lockstep form, replacing the paper's strict same-round
statement).** *After GST, given an honest validator at round `r`,
every honest validator reaches round `≥ r + 1` within 3Δ.*

**Proof.** Direct invocation of the post-GST scheduler-fairness
assumption (F-1a). Given an honest validator at round `r`, the
assumption gives a step `k'` within 3Δ wall-clock at which every
honest validator's local round is ≥ r + 1.

(The paper's §5 prose proof of L1 — "all honest must receive at
least one round-r block by GST+Δ; pull within 2Δ; accept 2f+1
round-(r-1) blocks; enter round r by GST+3Δ" — is the
*justification* for the fairness assumption itself, not a step in
the lemma's deductive proof. In a paper-faithful presentation,
that justification belongs to the discussion of the network /
delivery model, not to L1's proof.)

### 2.2 Lemma 2 (rewrite)

**Lemma 2.** *After GST, an honest validator `v_i` at round `r`
enters round `r + 1` within 3Δ.*

**Proof.** Apply L1 to obtain a step within 3Δ at which every
honest validator (including `v_i`) is at round ≥ r + 1. Since the
local round counter is monotone and increments by at most one per
step, the intermediate-value argument extracts a step `k_c` within
the same 3Δ window at which `v_i`'s local round is exactly
`r + 1`.

### 2.3 Theorem 1 — Block availability (rewrite)

**Theorem 1.** *If an honest validator `v_i` outputs
`block_accept_i(B.d)` for some block `B`, then `v_i` eventually
outputs `block_store_i(B)`.*

**Proof.** By the protocol's action priority, the store action
(action 3) sits strictly above the round-advance action (action
4). Hence at every step where `v_i` advances its local round, the
store action must have been disabled — every block in `v_i`'s
local pool whose digest `v_i` has accepted has been stored.

Concretely: `v_i` accepts `B.d` at some step `k`; the
corresponding block `B` is in `v_i`'s pool from `k` onward (the
block pool is monotone). By Lemma 2 applied at any post-GST step,
`v_i` eventually advances its local round; let `k_a` be the step
of `v_i`'s next round-advance after `k`. At `k_a`, the store
action was disabled, so `B.d` was stored. Hence `v_i` has output
`block_store_i(B)` by step `k_a + 1`.

(The paper's existing T1 proof argues via ImPoA's "parents
referenced by f+1 subsequent blocks → at least one honest stored
the parents → pull → eventually stores". That argument relies on
a richer reception model. The action-priority argument above
discharges T1 with strictly weaker assumptions: it does not need
ImPoA, only the priority order and the round-advancement liveness
established by L2.)

### 2.4 Theorem 2 — Causal availability (rewrite)

**Theorem 2.** *If an honest `v_i` outputs `block_accept_i(B.d)`
for some block `B` in round `r`, then for every `B' ∈ causal(B)`,
`v_i` eventually outputs `block_accept_i(B'.d)`.*

**Proof.** The block-acceptance rule requires `v_i`'s having
already accepted every parent digest of any block it accepts.
Hence the set of digests `v_i` has accepted is closed under
causal-ancestor lookup at every step: if `v_i` has accepted `B.d`,
then `v_i` has accepted every `B'.d` reachable from `B` by parent
edges. The conclusion holds *at the step of `B`'s acceptance
itself* (no eventual quantifier required).

(The paper's existing T2 proof argues "either `v_i` has already
accepted the parents, or they are referenced by f+1 subsequent
blocks → ImPoA → eventual accept". Our `tryActFor`'s accept rule
collapses this disjunction by requiring direct parent-acceptance,
which makes T2 a structural trace invariant rather than an
eventual claim. This is a *modeling choice*; paper readers should
note that under the simpler accept rule, the ImPoA-based reasoning
is unnecessary for T2.)

### 2.5 Theorem 3 — Round-Progression (rewrite)

**Theorem 3.** *For each round `r ≥ 0`, at some step at least
2f+1 distinct validators have proposed for round `r`.*

**Proof.** Pick any honest validator `v_w` (the honest set is
nonempty, with size ≥ 2f+1 by `n ≥ 3f+1` and Byzantine count ≤ f).
By iterated L1 starting from a post-GST step, there is a step
`k_target` at which every honest validator's local round is
≥ r + 1. By the protocol's propose-before-advance gate (action 1
above action 4): at every step where a validator's local round is
`R + 1`, that validator has emitted a propose op for every round
`r' ≤ R`. Hence at step `k_target`, all 2f+1 honest validators
have emitted propose ops for round `r`. Distinctness of authors
follows from the validator-IDs-distinct condition (paper §2).

(The paper's existing T3 proof uses "L1 → all honest reach same
round → 2f+1 honest emit round-r blocks". Our argument substitutes
"L1 → all honest reach round ≥ r + 1" (the lockstep form, F-1b),
which is sufficient and matches the assumption that drives the
proof.)

### 2.6 Theorem 4 — Round-Termination (rewrite)

**Theorem 4.** *For each round `r ≥ 0` and each honest validator
`v_i`, at some step `v_i` has accepted blocks proposed for round
`r` from at least 2f+1 distinct validators.*

**Proof.** Apply the argument of T3 to obtain a step `k_a` at
which `v_i` is at local round `r` and is about to advance to
`r + 1`. At `k_a`, the round-advance gate is enabled, which by
the paper's protocol requires that all registered validators have
proposed for round `r`. By the propose-op-implies-block-in-pool
correspondence (a structural fact about Beluga's `doPropose`),
the pool at `k_a` contains a round-`r` block for each of the
`n ≥ 2f+1` registered validators.

The accept action (action 2) sits above the advance action (action
4) in the priority order. Hence at `k_a`, accept was disabled —
every block in `v_i`'s pool either has its digest already in
`v_i`'s accept set, or has at least one parent digest `v_i` has
not accepted. By induction on round (downward from `r`): for any
block `B` in `v_i`'s pool at `k_a` with `B.r ≤ r`, all of `B`'s
parent digests correspond to round-`(B.r - 1)` blocks in the pool
at `k_a` (by the parents-in-pool structural invariant of Beluga's
`doPropose`); the inductive hypothesis gives `v_i` has accepted
those parents; hence `v_i` has accepted `B.d`. In particular,
`v_i` has accepted every round-`r` block in the pool at `k_a` —
giving 2f+1 distinct authors via the `digest = digest(round, author)`
canonical form (paper §2.1's block structure).

(The paper's existing T4 proof argues by induction on `r` with a
per-round step invoking T1 + T2 + ImPoA. Our argument replaces the
induction-on-`r` with a single induction-on-`B.r` *within* a fixed
advance step — a tighter argument that does not need to compose
T1 and T2.)

---

## Outlook

When the in-flight liveness rounds (paper §D.2 L8/L9/L11/L12/T6)
close, Stage 3 will fold their findings in. T1/T3/T4 of paper §5
are now mechanized; the rewrites above are the load-bearing
arguments. The §D.2 round may surface additional items in the
same shape as F-8(c) — implicit universe / qualifier issues
exposed by literal formalization.
