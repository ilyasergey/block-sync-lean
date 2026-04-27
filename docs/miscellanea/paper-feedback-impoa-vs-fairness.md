# ImPoA vs. SchedulerFairness — what each does, and why we need ours

> **Companion to**
> [`paper-feedback-l1-l2-fairness.md`](paper-feedback-l1-l2-fairness.md).
> That doc argues that the paper's L1/L2 proofs need a
> scheduler-fairness assumption that the paper does not state. This
> doc addresses the natural follow-up: *can ImPoA (paper §4.3) give
> us round progress in place of scheduler fairness?* Short answer:
> no, but the paper does have a different liveness mechanism
> (the per-round timeout `T_rd = 4Δ`) which our SchedulerFairness
> is the abstract form of.

## The question

Our Beluga §5 mechanization assumes `SchedulerFairness`:

> *After GST, whenever some honest validator is at round `r`, every
> honest validator reaches round `≥ r + 1` within `3Δ`.*

The paper does not state this. It does, however, describe ImPoA
extensively (paper §4.3). A reader might suspect that ImPoA is the
paper's substitute for scheduler fairness — that ImPoA somehow
gives round progress in place of an active-scheduling assumption.
This doc argues that suspicion is wrong, and identifies the actual
mechanism the paper uses.

## What ImPoA actually does

Paper §4.3 (ImPoA-based hybrid pull protocol):

> *A block `B` is implicitly available if it is referenced (via
> strong or weak links) by at least f+1 blocks from subsequent
> rounds. Note that a validator references B only if it (i)
> receives B, and (ii) can verify the availability of B's causal
> history.*

ImPoA is a **correctness + bandwidth** mechanism, not a liveness
one:

- **Correctness**: A validator can safely accept a block whose
  parents it has not directly received, *if* enough subsequent
  references prove the parents are stored by at least one honest
  party. This decouples accept-progress from direct-delivery
  bottlenecks.
- **Bandwidth**: Avoids re-broadcasting; validators pull only when
  needed, using f+1 references as the availability witness.

Critically, ImPoA is a **passive structural property** of blocks
in the DAG. It does not say "honest validators advance rounds";
it says "*if* a validator wants to accept B and B has f+1
referencers, then it can". The advance still has to be *triggered*
by something else.

## The paper's actual liveness mechanism: the timeout `T_rd = 4Δ`

Paper §4.2 (admission control + round advancement):

> *A validator `v_i` advances to round `r` if it either: (i)
> receives 2f+1 blocks from round `r − 1` whose creators have
> reputations above [a threshold]; or (ii) the per-round timeout
> `T_rd` expires, which is set to `4Δ` to ensure all honest
> blocks are received (Lemma 1).*

The **per-round timeout `T_rd = 4Δ`** is the load-bearing liveness
mechanism. It guarantees that, regardless of network conditions
or adversarial Byzantine behavior, an honest validator advances
within `4Δ` of entering a round. Combined with `Δ`-delivery
(paper §2) and the push protocol's parent-acceptance rules
(§4.2), this gives the L1 conclusion (`3Δ` global catch-up).

ImPoA participates in this argument — it is what allows
"acceptance via f+1 references" without waiting for direct
delivery of every parent — but ImPoA alone, *without* the
timeout, does not give liveness. With ImPoA but no timeout,
honest validators could in principle wait forever for 2f+1
quorum-acceptable round-`r` blocks.

## Can ImPoA give us round progress without scheduler fairness?

**No.** Concretely:

1. ImPoA is a structural property of the DAG: "B is implicitly
   available iff f+1 subsequent blocks reference it". This is
   a static predicate on the current state, not a liveness claim.

2. To advance a round, a validator must execute the round-advance
   action. ImPoA does not trigger any action; it only enables one
   (acceptance) when the validator chooses to act.

3. If the trace's scheduler never selects `vid_a` (an honest
   validator), `vid_a` never acts. ImPoA does not help —
   `vid_a` doesn't even check whether blocks are implicitly
   available, because `vid_a` is never running.

So ImPoA is necessary for the *content* of the round-progress
argument — it is how acceptance escapes direct-delivery
dependency — but it is not sufficient on its own. **Liveness
requires an active mechanism: either the timeout `T_rd` (paper)
or scheduler fairness (our abstraction).**

## Can we derive SchedulerFairness from ImPoA + the paper's other
mechanisms?

**Yes, in principle, but only with a richer trace model.**

Sketch of the derivation:

| Paper mechanism | Lean equivalent (would need to add) |
|-----------------|-------------------------------------|
| Per-validator local clock | Track `time` *per validator*, not just per step |
| Network delivery within `Δ` post-GST | Already partially modeled by `PartiallySynchronous`; would need to be tightened to "honest-to-honest message arrives within `Δ`" |
| Push protocol | A `messagesInFlight` field on `BelugaState`; honest doPropose appends |
| Per-round timeout `T_rd = 4Δ` | A new `tryActFor` branch: advance if `time(vid) - lastRoundEntry(vid) ≥ 4Δ` |
| ImPoA-based pull | Additional accept rule: accept B if f+1 in-pool references and parents accepted (current rule) OR f+1 references and pull-availability check succeeds |

With those additions, `SchedulerFairness` becomes a *theorem*
about `belugaTrace`, derivable from:

- Δ-delivery (post-GST).
- Push protocol delivers blocks.
- Timeout fires after 4Δ.
- ImPoA enables acceptance without waiting for direct parent delivery.

The structural argument matches paper L1: H pushes round-r block;
delivered to all in Δ; each honest accepts within 2Δ via direct
or ImPoA path; advance fires by Δ + 2Δ + 4Δ-bounded timeout
within 3Δ overall.

**This is meaningful future work** but a substantial scope
extension: it requires modeling messages, per-validator time, and
the timeout — currently all abstracted away. The current trace is
state-only; making it network-aware roughly doubles the model
complexity.

## Where does this leave us?

The current factoring is sound but coarse:

- Our `SchedulerFairness` axiomatizes paper L1's *conclusion*. It
  is the smallest assumption that lets §5's main theorems go
  through against our state-only trace model.
- The paper's actual mechanism is the per-round timeout `T_rd =
  4Δ` plus ImPoA + push + Δ-delivery. Together these *imply*
  something equivalent to our SchedulerFairness, but the
  derivation requires modeling primitives (messages, per-validator
  time, timeout) we currently abstract.
- ImPoA alone does **not** substitute for scheduler fairness —
  ImPoA is passive; liveness requires an active mechanism, which
  in the paper is the timeout.

## Recommendation

Three options, in increasing scope:

1. **Document the abstraction explicitly** (smallest scope).
   Make clear in the bundle docstring that `SchedulerFairness` is
   the abstract form of "paper §4.2's `T_rd = 4Δ` timeout +
   §2's Δ-delivery + §4.3's ImPoA pull, factored into a single
   trace-level claim." We have done this in this commit.

2. **Refactor the bundle** (medium scope). Replace
   `SchedulerFairness` with two finer-grained assumptions: a
   per-validator-time model + a timeout axiom. This makes the
   *factoring* paper-faithful but the load-bearing axiom is still
   not derived; `SchedulerFairness` becomes a one-line corollary.

3. **Refine the trace model** (large scope). Add message-flight
   state and per-validator time to `BelugaState`; extend
   `tryActFor` with the timeout branch; derive
   `SchedulerFairness` as a theorem. This is the paper-faithful
   formalization in full. ~2–3 weeks of mechanization work.

For the present mechanization, (1) is what we've done. (3) is the
right long-term target; (2) is a reasonable intermediate.

## Why the paper's framing doesn't make this obvious

The paper's prose proofs of L1 and L2 weave timeout and ImPoA
together implicitly: a sentence like "by ImPoA, all honest can
synchronize missing ancestors within `2Δ`" reads as if ImPoA
delivers the `2Δ` bound, when in fact ImPoA gives only the
*shape* of the synchronization (acceptance via f+1 references)
and the `2Δ` bound comes from Δ-delivery plus the validator
acting on received messages within bounded time.

A reader who is fluent in distributed-systems prose will fill in
the missing "validators act within bounded time" assumption
silently. A proof assistant cannot. Hence our explicit
`SchedulerFairness` axiom — same assumption, just written down.
