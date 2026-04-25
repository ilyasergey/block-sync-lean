# Note for the Beluga authors — a missing assumption in Lemmas 1 and 2

## Context

We have been mechanizing the Beluga protocol in a proof assistant
(Lean 4) following the paper's §2 abstract block-synchronizer
specification and §4 concrete protocol. While attempting to discharge
the proofs of **Lemma 1** and **Lemma 2** (paper §5) against our
formal model, we identified what appears to be a missing assumption
that the paper's prose proofs use implicitly. This note describes
the issue in the paper's own terminology — no proof-assistant
background needed.

The bottom line: as currently stated, neither Lemma 1 nor Lemma 2
follows from the paper's explicit assumptions. They become provable
once a *scheduler fairness* assumption is added — something the paper
appears to take for granted but never states. We suggest making it
explicit.

## The lemmas, as stated in the paper

> **Lemma 1.** After GST, all honest validators will enter the same
> round within 3Δ.

> **Lemma 2.** After GST, if an honest validator `v_i` enters round
> `r` at time `t_r`, and all honest validators have created and
> disseminated their round `r` blocks by time `t_r`, then all honest
> validators will be able to enter round `r + 1` by time `t_r + 3Δ`.

## What the paper assumes explicitly

We can find the following assumptions in the paper:

- **Network.** Post-GST, every message between two honest validators
  is delivered within `Δ` (partial synchrony).
- **Quorum.** `n ≥ 3f + 1`; honest validators wait for `2f + 1`
  parents before advancing rounds.
- **Honest behavior.** Honest validators follow the protocol of §4
  faithfully: they propose, accept, store, and advance according to
  the rules; they do not equivocate.
- **Assumption 1 (latency triangle, App. C.2).** Direct honest-to-
  honest delivery is faster than any relay through an intermediate
  validator.

What the paper *does not* state explicitly is anything that constrains
**how often, or how promptly, an honest validator takes its local
steps.** The proofs of L1 and L2 silently assume that an honest
validator is "always active" — that it processes incoming blocks,
proposes its own block, and advances its round counter promptly once
the protocol's preconditions are satisfied. We will call this the
**scheduler-fairness** assumption.

Without that assumption, both lemmas are falsifiable.

## Counterexample (paper-level, no Lean involved)

Take the smallest interesting setting: `n = 4`, `f = 1`, four honest
validators `v_0, v_1, v_2, v_3`, GST = 0, Δ = 10. Following the
paper's protocol exactly:

### Why Lemma 1 fails

Consider the following execution. After GST, the network behaves as
the paper assumes: every honest-to-honest message is delivered within
Δ = 10 time units. However, the *local processing schedule* of
honest validators is asymmetric:

- `v_0` is *fast*: it processes its inbox, proposes round-0 blocks,
  receives `2f + 1 = 3` round-0 parents, and advances to round 1 by
  local time 5.
- `v_1`, `v_2`, `v_3` are *slow*: although they receive all the
  necessary round-0 messages within Δ of GST, they do not get
  scheduled to take any local action during the interval `[0, 30]`.
  (Perhaps the underlying OS scheduler hasn't given them CPU time;
  perhaps they are batching messages; the paper doesn't preclude
  any of these.)

At time 30 = GST + 3Δ, `v_0` is in round 1 while `v_1`, `v_2`, `v_3`
are still in round 0. Lemma 1's "all honest validators … within 3Δ"
fails: not all honest validators are in the same round.

### Why Lemma 2 fails

Same setup. Suppose at time `t_r = 5`, `v_0` (now in round 1) has
created and disseminated its round-1 block. The paper's hypothesis
requires "*all* honest validators have created and disseminated their
round `r` blocks by time `t_r`." If we strengthen the example so
that `v_1`, `v_2`, `v_3` *also* manage to create and disseminate
their round-1 blocks by `t_r = 5`, the hypothesis is satisfied. But
those three validators may still not take any *advancement* step
between `t_r = 5` and `t_r + 3Δ = 35`. Their inboxes contain enough
round-1 parents to advance, but they have not been scheduled to do so.
Hence `v_1`, `v_2`, `v_3` remain in round 1 at `t_r + 3Δ`. Lemma 2's
"all honest validators will be able to enter round `r + 1` by time
`t_r + 3Δ`" fails.

## What the proofs implicitly use

Reading the paper's prose proofs of L1 and L2 carefully, every step
that says "by time `t + Δ`, validator `v` accepts/advances …" relies
on an implicit "as soon as `v` can act, it does." Two examples:

> *"By Assumption 1 (latency triangle), if `v_i` is honest and sends
> `B_i^{r-1}` to `v_j`, then `v_j` receives `B_i^{r-1}` directly
> before receiving it via an intermediate validator …"*

This says `v_j` *receives* the block within Δ — true under the
paper's network assumption. It does not say `v_j` *processes* the
block within Δ. The proof then continues "*hence `v_j` accepts
`B_i^{r-1}` …*" — silently equating receipt with processing.

> *"Even though some honest validators may need to synchronize
> missing ancestors to accept round `r` blocks, they can accept these
> blocks via the pull protocol within `2Δ`."*

"Within 2Δ" is a network-delay claim. To turn this into a "validator
has updated its local state within 2Δ" claim, you need to know the
validator actually executed its accept logic within that window.

## Suggested fix

Make the scheduler-fairness assumption explicit. A minimal form,
phrased in the paper's terminology:

> **Assumption 2 (scheduler fairness).** *Post-GST, whenever an
> honest validator `v` is in a state where the protocol of §4
> enables a local action (propose, accept, store, or advance), `v`
> performs that action within Δ of becoming enabled.*

Under Assumption 2, both Lemma 1 and Lemma 2 follow as the paper's
prose argues — the implicit "validator processes promptly" step is
now explicit.

Variants of this assumption that we considered:

- **Stronger.** Assume a global clock and *all* honest validators
  take simultaneous local steps every Δ. Closer to the paper's
  intuition but harder to justify in an asynchronous setting.
- **Weaker.** Assume only that honest validators eventually act
  (no rate bound). Sufficient for *eventual* round progression but
  not for the paper's tight 3Δ bound.

The "within Δ of becoming enabled" version above is the smallest
strengthening that lets the paper's 3Δ bounds go through.

## Why a mechanization caught this

Implicit assumptions of the form "the validator does X promptly"
are routinely invisible to a human reader who has the right
intuition about how distributed protocols are operationalized.
A proof assistant has no such intuition: it requires every step
of a proof to be discharged by something explicit in the
assumptions or the model. Our model of §4 is faithful to the
paper's described protocol; what it lacks is a constraint on how
validators are scheduled. Adding any of the variants above closes
the gap.

This is, in our experience, exactly the class of finding that
mechanization is best at — the missing-step-because-everyone-
agrees-it's-obvious kind. The paper's protocol is correct; the
proofs of L1 and L2 are correct *under* the implicit assumption;
we just suggest writing the assumption down.

## Open questions for the authors

1. Is the suggested **Assumption 2** the intended scheduler-fairness
   assumption, or did you have a different one in mind (e.g., fully
   synchronous rounds)?
2. Does the same assumption suffice for the App. C.2 latency lemmas
   (L3–L5), or is something stronger needed there? (We needed
   Assumption 1 — the latency triangle — explicitly for L4 and L5.)
3. Is the assumption already implicit in the paper's reference to
   "the scheduler" in §2, and we have just been reading too literally?

We're happy to share the mechanization or further details if it
would help. The protocol itself appears sound under any of the
fairness variants we tried.
