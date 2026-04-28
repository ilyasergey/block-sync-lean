# Round-02 paper review — findings against the round-01 audit

A focused audit of the revised paper (`Block_Sync_Project2.pdf` in
this folder) against the Stage-1 + Stage-2 recommendations from
[`../round-01/`](../round-01/). For each round-01 finding (F-1
through F-13), we report whether the round-02 revision addresses
it and, where applicable, what remains. We also record new
observations introduced by the round-02 changes themselves
(notably the revised Lemma 1, the new round-advancement rule
(iii), and the `T_rd = 5Δ` retiming).

The §5 Lemma 1 of the revised paper has been **formalized and
proved** in Lean as `lemma1_paper_round02` in
[`BlockSynchroniser/Beluga/Theorems.lean`](../../BlockSynchroniser/Beluga/Theorems.lean);
see §3 below.

---

## 1. Status of round-01 findings against round-02

| ID | Round-01 status | Round-02 status | Where |
|---|---|---|---|
| **F-1** (per-action liveness assumption) | Open (paper-side); resolved in our model via `BelugaPartialSynchrony` | **Not addressed** | §5 prose still uses "honest validators must receive blocks within `Δ`" without naming a per-action liveness primitive |
| **F-1b** (L1 wording) | Open | **Partially addressed** | L1 restated; "the same round" replaced by "all honest validators will enter round `r` by `t + 4Δ`". Closer to the lockstep-progress form, but the "by `t + 4Δ`" wording remains ambiguous (see §2.1 below). |
| **F-1c** (pull mechanism modelling) | Resolved on our side | n/a | This is mechanization-internal, not a paper finding. |
| **F-2** (pin `n = 3f + 1`) | Open | ✅ **Resolved** | Round-02 §2: *"We assume a set V of `n = 3f + 1` validators"* |
| **F-3** (cross-block honest non-equivocation forms) | Open | ✅ **Resolved (b); partial (a)** | Round-02 §D.3 enumerates: *"(i) Honest validators only create at most one block per round (i.e., honest validators do not equivocate by definition)"* — that is F-3(b) verbatim. F-3(a) (cross-block parent-set agreement) follows as a corollary of (b) but is not separately stated. |
| **F-4** (cite Assumption 1 / latency triangle in L4, L5) | Open | **Not addressed** | The C.2 lemma proofs still use the `Δ`-delivery step without naming Assumption 1 at the call site. |
| **F-5** (DAG invariants in L13/L15) | Open | ✅ **Resolved** | Round-02 §D.3 enumerates the four DAG invariants explicitly: *"(i) Honest validators only create at most one block per round; (ii) Each block must reference as parents `2f+1` blocks created by `2f+1` distinct validators from the immediately preceding round; (iii) A block is valid only if its creator corresponds to a registered validator in V …; (iv) The block digest is derived from hashing the block …"*. Items (i)–(iv) cover F-5(2), F-5(1), F-5(4), and F-5(3) (with F-3(b) overlap on (i)). |
| **F-6** (reputation update `r-1` vs `r-2`) | Open | ✅ **Resolved** | Round-02 §4.2 prose uses `r-1`; Figure 8 line 27 also uses `r-1`. The off-by-one is gone. |
| **F-7** (T7 conflates safety with liveness) | Open | ✅ **Resolved** | T7 restated as **prefix-consistency** of ordered transaction sequences: *"S_i and S_j are prefix-consistent, i.e., one is a prefix of the other"*. The proof now goes through Lemma 16 + a backward-induction over leader-block rounds (Lemma 16 → consistent decisions per round → consistent ordering of to-commit leader blocks and their causal histories). Matches our Stage-1 recommendation #1 ("restate T7's conclusion to prefix-consistency"). |
| **F-8** (validator-ID assumptions) | Open | ✅ **Resolved (a); partial (c)** | Round-02 §2: *"a set V of `n = 3f + 1` validators … `{v_0, …, v_{n−1}}`"*. The contiguous-IDs form (F-8(a), the load-bearing one) is now explicit. F-8(c) (the BFT bound's universe being the registered set) is still implicit but is editorial-only. |
| **F-11** (block-digest determinism) | Open | ✅ **Resolved** | Round-02 §D.3: *"The block digest is derived from hashing the block and can be used to identify the same block, where an identical digest implies the same block."* |
| **F-12** (ImPoA-free §5 proofs) | Open | **Not addressed** | T1 and T2 proofs in round-02 §5 still route through ImPoA / `f+1`-references arguments. Our Stage-2 alternative sketches (action-priority based) remain available for adoption. |
| **F-13** (accept-store atomicity) | Open | **Not addressed** | Round-02 §5 T1 proof still implicitly assumes accept ⇒ store atomicity; Figure 8 still has both outputs from a single procedure step. |

**Round-02 closes 6 of the 12 substantive findings (F-2, F-5, F-6,
F-7, F-8, F-11) and partially addresses 2 more (F-1b, F-3).** Four
findings remain open as paper-side work for round 3 (F-1, F-4,
F-12, F-13). F-1c and F-7 are now closed end-to-end.

---

## 2. New observations introduced by round-02 changes

### 2.1. Revised Lemma 1: the "by `t + 4Δ`" wording is still semantically ambiguous

**Round-02 statement.**
> *(Lemma 1.) After GST, if round `r` is the highest round that
> honest validators are in at some time `t`, then all honest
> validators will enter round `r` by `t + 4Δ`.*

This is closer to the lockstep-progress form recommended in F-1b
(no "the same round" wording), but the phrase **"all honest
validators will enter round `r` by `t + 4Δ`"** retains the
simultaneity ambiguity. Two readings are consistent with the
prose:

- **(simultaneous.)** *There exists a single time `t' ≤ t + 4Δ`
  at which every honest validator is at round `≥ r`.*
- **(per-validator reachability.)** *Each honest validator is at
  round `≥ r` at some time `≤ t + 4Δ` (possibly different times
  for different validators).*

The L1 proof's case analysis ("by time `t + 3Δ`, all validators
have entered round `r` and created their round-`r` blocks") and
the T3 proof ("all honest validators can enter the same round
(w.l.o.g, at round `r`) within `4Δ`") suggest the **simultaneous**
reading is the intended one. The same-round wording in T3
mirrors the round-01 L1 wording flagged by F-1b — only the time
bound has been relaxed from `3Δ` to `4Δ`, not the simultaneity
claim.

**Why it matters.** The simultaneous form is what the paper's
own proofs cite (e.g., T3: *"all honest validators must be able
to create and disseminate their round-`r` blocks by time
`GST + 4Δ`"*); the per-validator-reachability form is weaker and
would not deliver that conclusion in one citation. So either
reading is internally consistent, but the wording does not pin
down which one is intended.

**Suggested fix.** State L1 as a single-time-witness claim:

> *(L1, suggested wording.) After GST, if round `r` is the highest
> round any honest validator is in at some time `t`, there is a
> time `t' ≤ t + 4Δ` at which every honest validator is at round
> `≥ r`.*

The single-`t'` quantifier order makes the simultaneity explicit
and matches the way L1 is consumed in T3. Mechanization-wise,
this is the form we have proved (`lemma1_paper_round02`, see §3).

### 2.2. The new advancement rule (iii) is ambiguously stated

**Round-02 §4.2 (page 7).**
> *Specifically, a validator `v_i` advances to round `r` if: (i) it
> receives `2f+1` blocks from round `r−1` whose creators have
> reputations above a threshold `R_t = R_{2f+1} − R_L` …; or (ii)
> it is in round `r−1`, and the per-round timeout `T_rd` expires,
> which is set to `5Δ` to ensure all honest blocks are received
> (Lemma 1); or (iii) it is in round `< r−1`.*

Read literally with `r` as the target round, rule (iii) says: *if
`v_i` is in any round `< r-1`, it can advance to round `r`*. This
is a "skip-ahead" rule that lets `v_i` jump arbitrarily far up the
round ladder — over `r-2`, `r-1`, etc. — without intermediate
round-r-1 blocks.

But the L1 proof of case 2 reads:
> *"validators in `V_slow` advance to round `r − 1` immediately
> and create their round `r-1` blocks at time `t + 3Δ`."*

Here `V_slow` consists of honest validators in any round `< r-1`,
and they all advance to round `r-1` (one less than the highest
known round). They do **not** skip to round `r` — the proof needs
them to *create round-`r-1` blocks*, which requires going through
round `r-1` and gathering its `2f+1` round-`r-2` parents.

So rule (iii) is being applied with the meta-quantifier
*"`r` ≔ (highest known round) − 1"*: a validator in round
`< (highest)−1` can advance to round `(highest)−1`. This is a
"catch-up to almost the leader" rule, not a skip-ahead. The rule
statement in §4.2 does not surface this re-quantification.

**Why it matters.** The two readings have different protocol
behavior:

- *Skip-ahead.* `v_i` jumps to round `r` without ever creating
  round-`r-1` blocks. Round `r-1`'s `2f+1`-creator quorum is
  *not* contributed to by `v_i`, so subsequent rounds might lack
  the `2f+1` round-`r-1` blocks they need as parents.
- *Catch-up to round `r-1`.* `v_i` creates a round-`r-1` block,
  contributing to round `r-1`'s `2f+1`-creator quorum. This is
  what the L1 proof and T3 proof require.

Without disambiguation, a literal protocol implementation could
adopt either; only one supports the §5 proofs.

**Suggested fix.** State rule (iii) directly in catch-up form:

> *(iii) `v_i` is in some round `r' < r-1` and observes (in its
> view) some block of round ≥ `r`; in this case `v_i` advances
> directly to round `r-1` (without waiting for `T_rd` or for
> `2f+1` round-`r-2` quorum), creates its round-`r-1` block in
> the normal way, and then proceeds with rule (i) or (ii) for
> subsequent advances.*

This makes the trigger explicit ("observed a round-`r` block")
and the target explicit (`r-1`, not `r`).

### 2.3. `T_rd = 5Δ` is consistent with the new L1

The retiming `T_rd : 4Δ → 5Δ` is correct under the revised L1:

- L1 gives "all honest validators are at round `≥ r` by
  `t + 4Δ`" (assuming the simultaneity reading).
- Once all `2f+1` honest validators are at round `r`, each
  creates its round-`r` block immediately upon entering `r` (the
  `create_new_block` action in Figure 8).
- By push delivery (`Δ`-bounded post-GST), every honest validator
  receives the `2f+1` round-`r` blocks within `Δ` of their
  creation, i.e., by time `t + 5Δ`.

So `T_rd = 5Δ` is the smallest timeout that lets rule (ii) fire
*after* all `2f+1` honest round-`r` blocks have been received,
which is what rule (ii) is meant to ensure. The `4Δ → 5Δ`
retiming is a direct consequence of the `3Δ → 4Δ` L1 retiming.

This change does not affect any of our §5 proofs: in our model,
round advancement is governed by the `actionScheduling`
(per-action liveness) primitive, not by the wall-clock timeout
gate. The timeout value sits in the protocol's `tryActFor`
predicate but is never consumed by the §5 lemma proofs (the
fairness assumption short-circuits it). We have not yet bumped
the value `4` in our executable protocol's timeout gate — see
§3.3 below for the small consequence.

### 2.4. The `V_slow ≠ ∅` case in the L1 proof relaxes the gap-1 invariant

The round-01 paper's L1 proof implicitly assumes a *strict*
round-spread invariant: at any post-GST time, all honest
validators are within one round of each other. The round-02
proof explicitly admits the case `V_slow ≠ ∅`, where some
validators are in round `< r-1` (gap > 1). This is the case the
new advancement rule (iii) is designed to handle.

**Implication for verification.** A mechanization that takes
"gap ≤ 1 post-GST" as a primitive (as our Stage-2 bundle's
`boundedRoundSpread` does) is an over-commitment relative to
what the round-02 protocol actually maintains: the round-02
protocol can have gap `> 1` *transiently* until rule (iii) fires
and re-establishes the smaller gap. A faithful mechanization of
the round-02 protocol's invariant would need to either:

1. Weaken `boundedRoundSpread` to "gap eventually `≤ 1` after
   `4Δ` post-GST" (matching the L1 conclusion), or
2. Strengthen the fairness assumption to model rule (iii)
   explicitly as a per-validator catch-up step.

In our current model the `boundedRoundSpread` is an assumption,
not a derived fact, so this is a mechanization-side observation
not a paper-side finding. We do however report it here because
the round-02 paper's L1 proof structure is what surfaces the
distinction.

### 2.5. Lemma 2 disappeared from §5

The round-01 paper had a Lemma 2 ("round-to-round latency
≤ 3Δ") sandwiched between L1 and T1. The round-02 §5 contains
only L1, T1, T2, T3, T4 — Lemma 2 is no longer stated. This is
not a problem for the §5 theorems (T3's proof folds in the
round-latency bound directly), but readers of the round-01
paper who cite "L2" in downstream work will find no L2 in the
round-02 reference. If this was intentional, a footnote or
removal-note would help; if unintentional, L2 should be
restored or its content folded into L1.

We have kept our `lemma2_round_latency` in the formalization as
a derived consequence of L1 — useful as a proof-structure
checkpoint but not load-bearing. (See §3 below.)

---

## 3. Mechanization of the revised Lemma 1

### 3.1. The new Lean theorem

The round-02 statement of L1 is formalized as:

```
theorem lemma1_paper_round02
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h : BelugaWithPullFairness system time) :
    ∀ (r : Round) (k₀ : Nat),
      time k₀ ≥ system.GST →
      (∃ vid_ref bv_ref,
        isHonestValidator system vid_ref = true ∧
        (networkTraceWithPull system time k₀).base.getValidator vid_ref = some bv_ref ∧
        bv_ref.currentRound = r) →
      ∃ k', k₀ ≤ k' ∧ time k' ≤ time k₀ + 4 * system.Δ ∧
        ∀ vid, isHonestValidator system vid = true →
          ∃ bv, (networkTraceWithPull system time k').base.getValidator vid = some bv ∧
                bv.currentRound ≥ r
```

(in
[`BlockSynchroniser/Beluga/Theorems.lean`](../../BlockSynchroniser/Beluga/Theorems.lean)).

This is the **simultaneous** reading of round-02 L1 (see §2.1
above): a single step `k'` within `4Δ` at which every honest
validator is at round `≥ r`. The "highest round" hypothesis is
formalized as the existence of an honest validator at round `r`
at step `k₀`; the upper-bound part of "highest" (no honest
validator is at round `> r`) is not consumed by the proof, so
we omit it from the hypothesis without weakening the conclusion.

### 3.2. The proof is a one-shot derivation from the round-01 L1

The proof takes the existing `lemma1_honest_round_entry`
(round-01 L1, with bound `3Δ` and conclusion `≥ r + 1`) and:

1. Invokes it on the same witness `vid_ref` at round `r`,
   yielding a step `k'` within `3Δ` at which every honest
   validator is at round `≥ r + 1`.
2. Weakens `3Δ ≤ 4Δ` (the round-02 bound).
3. Weakens `≥ r + 1` to `≥ r` (the round-02 conclusion).

The round-02 L1 is therefore a **strict consequence** of our
existing round-01 L1 mechanization — the simultaneity-and-bound
relaxation that the paper's revision performs is provable in 5
lines on top of what we already have. No new fairness
assumption, no new protocol mechanism, no new mechanization
primitive is required.

### 3.3. What this tells us about the bundle

A noteworthy observation: our model's `boundedRoundSpread`
primitive — *post-GST, the rounds of any two honest validators
differ by at most one* — is **strictly stronger** than what
round-02 L1 needs. With `boundedRoundSpread`, the case
`V_slow ≠ ∅` from the round-02 L1 proof never arises (no honest
validator is at round `< r-1`), so the round-02 advancement
rule (iii) is redundant in the model.

Two ways to read this:

- **(A) `boundedRoundSpread` is the right paper-level
  abstraction.** The round-02 paper introduces rule (iii) as a
  catch-up mechanism precisely so that the gap-1 invariant
  *holds in steady state*; modelling the steady state directly
  (as our bundle does) is a valid and more abstract level for
  §5's reasoning.
- **(B) `boundedRoundSpread` over-commits.** Honest validators
  in transient states (immediately post-GST, before rule (iii)
  has fired) can have larger gaps; modelling them directly
  would require relaxing the invariant and lifting rule (iii)
  into the protocol step.

Both readings are tenable. Reading (A) is what the §5 prose
seems to want (it cites L1 as a bound, not as a derivation of
the gap), and our bundle is consistent with this reading.
Reading (B) is what a §4.2-faithful protocol mechanization
would adopt; we have not pursued it because it requires a model
change with no §5 payoff.

We do **not** propose changing `boundedRoundSpread`. We do
propose that the paper, when stating L1, distinguish between
"the §5-level abstraction (gap-1 in steady state)" and "the
§4.2-level mechanism (rule (iii) re-establishes the gap)" so
the two layers are visibly separated.

### 3.4. The `T_rd = 5Δ` value in the protocol-layer code

Our executable protocol (`networkStepWithPull`'s timeout gate)
currently uses `4Δ` as the per-round timeout, matching the
round-01 paper. The round-02 retiming to `5Δ` would be a
one-line change in
[`BlockSynchroniser/Beluga/Network.lean`](../../BlockSynchroniser/Beluga/Network.lean),
inside the definition of `NetworkState.timeoutFired`. Since
none of the §5 proofs consume the specific timeout value (they
go through `actionScheduling`, not through the timeout gate),
making this change is mechanically safe. We have **not** made
the change in this round to keep the deliverable focused on
the L1 statement and proof; it is a candidate cleanup for a
follow-up commit.

---

## 4. Stage-3 candidate edits

The following items remain as paper-side recommendations after
round-02. Each is a candidate for a Stage-3 paper-additions doc
once we settle on which to pursue.

### 4.1. Make L1's quantifier order explicit (§2.1 above)

Replace
> *all honest validators will enter round `r` by `t + 4Δ`*

with
> *there is a time `t' ≤ t + 4Δ` at which every honest validator
> is at round `≥ r`.*

This is a wording change with no proof-structure consequence.

### 4.2. Restate rule (iii) in catch-up form (§2.2 above)

Replace the §4.2 rule list's third clause
> *(iii) it is in round `< r−1`*

with the catch-up form
> *(iii) `v_i` is in some round `r' < r-1` and has observed a
> block of round ≥ `r` in its view; in this case `v_i` advances
> directly to round `r-1` and creates its round-`r-1` block.*

This makes the rule unambiguous and matches the L1 proof's
usage of it.

### 4.3. Retain the round-01 findings still open in round-02

Three round-01 paper-additions did not land in round-02 and we
recommend re-iterating them:

- **F-1: name the `BelugaPartialSynchrony` assumption** as a
  single bundle in §5, rather than letting the §5 proofs cite
  scheduler-fairness/in-pool-delivery implicitly. See
  Stage-2 §1.
- **F-12: rewrite T1 and T2 with the action-priority argument**
  (rather than via ImPoA). See Stage-2 §3, sketches for T1 and
  T2.
- **F-13: state accept/store atomicity (or split with action
  priority)** in §4 / Figure 8.

(F-4 — citing Assumption 1 in L4/L5 — is editorial-only; we
defer it to a future round.)

### 4.4. Restore or remove L2 (§2.5 above)

Decide whether L2's removal from §5 was intentional. If yes, a
footnote noting the consolidation; if no, restore the lemma or
fold its content into L1.

### 4.5. Refactor: bundle split into `BelugaPartialSynchrony` + `BelugaWithPullFairness` ✅ done

The paper author's response to Stage-2 noted that the original
bundle's item (3) — *"every honest validator advances rounds
within Δ"* — is **too strong**: a validator in round `r-1` with
no `2f+1`-quorum and no round-`r` sighting must wait up to `T_rd
= 5Δ`, not Δ. The unconditional "within Δ" form overstates what
the §4.2 rules (i), (ii), (iii) actually deliver.

We refactored the bundle accordingly:

- **`BelugaPartialSynchrony`** (the new weaker bundle) drops
  `actionScheduling` and adds **`CatchUpLiveness`** — paper §4.2
  rules (i)/(iii) in event-triggered form: *if honest `vid` is
  at a strictly lower round than some honest `vid_lead`, then
  `vid` catches up to `vid_lead`'s round within `4Δ`.* No
  advancement claim is made when no leader is ahead, so the
  `T_rd = 5Δ` rule-(ii) timeout is preserved untouched. The
  `4Δ` decomposes as `Δ` (push delivery) + `2Δ` (push/pull/ImPoA
  acceptance) + `Δ` (per-action scheduling for rule (i)/(iii)).

- **`BelugaWithPullFairness`** now `extends
  BelugaPartialSynchrony` (Lean record inheritance) and adds
  back `actionScheduling` as an extra field. Existing proofs of
  the round-01 L1, L2, T1–T4 continue to consume the stronger
  bundle without modification.

- **`lemma1_paper_round02`** is re-proved against
  `BelugaPartialSynchrony` alone — no `actionScheduling`
  required. The proof iterates over `system.validators`,
  applying `catchUpLiveness` per validator at round `< r` (with
  `vid_lead = vid_ref`, the witness honest validator at the
  highest round `r`), then takes the max of per-validator
  catch-up steps and uses round monotonicity to extend each
  catch-up to the common max. The `time(max k₁ k₂)` bound is
  discharged by case-splitting on `k₁ ≤ k₂`.

The result: the round-02 Lemma 1 is now mechanically derivable
from the paper-faithful weaker assumption set, mirroring the
round-02 paper's proof structure (event-triggered advancement +
delivery + acceptance) rather than the over-strong "advances
within Δ" assumption the author rejected. The deeper refactor
that would *also* demote `boundedRoundSpread` to a derived
theorem (and lift rules (i)/(iii) into the protocol step) is
deferred.

---

## 5. Summary

Round-02 closes 6 of the 12 substantive findings outright (F-2,
F-5, F-6, F-7, F-8, F-11) and partially addresses 2 more (F-1b,
F-3). Four findings remain open paper-side (F-1, F-4, F-12,
F-13). The revised Lemma 1 is provable from our existing bundle
in 5 lines as `lemma1_paper_round02`, since our gap-1
`boundedRoundSpread` primitive subsumes the case analysis the
round-02 proof performs.

The two new observations the round-02 changes surface are
wording-level: (a) the `t + 4Δ` clause in L1 still has a
simultaneity ambiguity that should be pinned down by the
quantifier order, and (b) the new advancement rule (iii) is
ambiguous about its target round (literal reading is
"skip-ahead"; the L1 proof requires "catch-up to round `r-1`").
Both are minor wording changes for round 3.
