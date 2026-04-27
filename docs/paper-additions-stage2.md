# Recommended additions to Beluga — Stage 2

This document is a focused list of edits we recommend to the Beluga
paper based on our formalization. It is **paper-only**: every
suggestion is phrased in the notation of the paper (Sections 2,
4, 5, and Appendix C–D). No Lean code is referenced.

For the full state of the formalization (paper→code map, current
proof status of every paper item) see
[`../formalization.md`](../formalization.md).
For the running log of paper-side observations the formalization
surfaced (with severities, affected sections, and recommended
actions per finding) see
[`mechanization-findings.md`](mechanization-findings.md).

The recommendations cluster into three groups:

1. **A single named liveness assumption** (Section 5) that the §5
   proofs already use silently, presented in paper-friendly form.
2. **Restated §5 lemmas and theorems** that match the actual content
   the paper's downstream arguments consume.
3. **Alternative proof sketches** for the §5 theorems, of roughly
   the same length as the existing prose, that follow more cleanly
   from the explicit assumption.

Where suggestions touch §4, those are listed at the end.

## 1. The single explicit assumption: `BelugaPartialSynchrony`

The paper's §5 prose proofs of L1, L2, T1–T4 silently use two
liveness facts that are not stated as assumptions:

- **(LS1) Per-action prompt scheduling.** Post-GST, whenever an
  honest validator is in a state where the §4.2 protocol enables
  a local action (`propose`, `accept`, `store`, or `advance`), the
  validator performs that action within `Δ`.
- **(LS2) Universal in-pool delivery.** Post-GST, every block in
  the global pool is eventually known to every honest validator
  (either through the §2 push channel of `Δ`-bounded honest-honest
  delivery, or through the §4.3 pull mechanism for blocks not
  received via push).

We recommend bundling all of the paper's §2 + §4.2 + §4.3 post-GST
liveness ingredients into a single assumption in §5, so that L1, L2,
T1–T4 can each be stated as "under `BelugaPartialSynchrony`,
…":

> **Assumption 2 (`BelugaPartialSynchrony`).** Post-GST, the
> following hold:
>
> 1. (Clock) The wall-clock time map `time(·)` is non-decreasing
>    and unbounded.
> 2. (Push delivery, §2) Every push message between honest
>    validators is delivered within `Δ`.
> 3. (Round-advance liveness, §4.2) Every honest validator
>    advances rounds within `Δ` (the per-round timeout
>    `T_rd = 4Δ` upper-bounds time spent in any one round).
> 4. (Protocol synchronization, §4.2) The rounds of any two
>    honest validators differ by at most one.
> 5. (Accept-action liveness, §4.2) When an honest validator has
>    an acceptable in-pool block, it accepts within `Δ`.
> 6. (In-pool delivery, §4.3) Every block in the global pool is
>    eventually known to every honest validator (push channel of
>    §2 ∪ pull mechanism of §4.3).

Items 1, 2, 4 are paper-stated already (they are what §2 calls
"partial synchrony" and what §4.2 calls "the protocol synchronizes
rounds"); items 3, 5, 6 are paper-implicit and are exactly the
additions this assumption surfaces.

**Faithfulness comment.** Items 3 and 5 are direct consequences of
the §4.2 timeout `T_rd = 4Δ` plus the timing model: an honest
validator that has been ready to act for more than `Δ` time would
already have advanced (otherwise the timeout fires). The paper's
prose treats them this way. Item 6 is the conclusion the §4.3 pull
mechanism is designed to deliver; the paper sketches the mechanism
(`pullCandidate`, push of pull requests, push of responses, push
delivery of resulting `block_propose`) but does not name the
conclusion. If the authors want, item 6 can be derived from items
2, 4 plus two atomic §4.3 primitives —
`PullRequestDelivery(req, k) ⇒ ∃ k', responder receives request
within Δ` and `PullResponseScheduling(req, k) ⇒ ∃ k', responder
schedules block_propose delivery within Δ` — but it is cleaner to
state the conclusion.

What this assumption is not: it does **not** make any claim about
Byzantine validators' messages, Byzantine pull responses, or the
adversary's scheduling. Item 6 ranges only over honest validators
as recipients; the *senders* of the pulled blocks may be anyone.
This is faithful to the paper's adversary model.

## 2. Restated §5 lemmas and theorems

Under `BelugaPartialSynchrony`, the §5 lemmas and theorems are
proved as stated in the paper, with one wording change to L1.

### L1 — round entry within 3Δ (restatement)

**Original (paper, current).**
> *After GST, all honest validators will enter the same round
> within 3Δ.*

**Suggested restatement.**
> *(L1.) After GST, given an honest validator at round `r` at
> some time `t`, every honest validator will be at round `≥ r + 1`
> by some time `t' ≤ t + 3Δ`.*

**Reason for the change.** The "the same round" wording is the
strict gap-0 form. The protocol, however, advances one validator at
a time: when one validator transitions from round `r` to round
`r + 1`, the others are still at `r` until they take their own
advance step. Across the 3Δ window post-GST, gap-0 states occur
*transiently* but gap-1 states are unavoidable (during a "round of
advances"). The strict form is therefore not provable from
`BelugaPartialSynchrony` alone; it would require atomic round
transitions in the model (i.e., have all validators advance
simultaneously when `allProposedFor` holds), or a separate witness
extraction.

The lockstep-progress form is what L1's downstream consumers
actually need — auditing every cite-site in the paper:

| Cite | What L1 is used for | Form needed |
|---|---|---|
| §4.2 timeout `T_rd = 4Δ` | "All honest blocks are received within 4Δ" | "All reach `≥ r + 1` within 3Δ" suffices |
| §5 L2 proof | "2f+1 honest validators have proposed for round `r`" | weaker form suffices via propose-before-advance gate |
| Happy-case timing analysis (§5) | "All created round-r blocks" | weaker form suffices |
| §D.2 L8 | "Every honest **will be able to enter** the same round" | the phrasing is already a reachability claim |
| §D.2 block-reception bound | "Every honest receives 2f+1 honest blocks" | weaker form suffices |
| §C.2 L4 | "All honest enter a common round" | used as a *naming convention* for the round |

None of the citations require gap-0. Adopting the lockstep-progress
form makes L1 provable from the cited assumptions and matches the
operational content the paper's own proofs consume.

### L2 — round-to-round latency ≤ 3Δ (no change)

L2 stands as the paper states it. The proof composes L1 with a
round-level intermediate-value argument: if validator `v` is at
round `r` at time `t`, and at round `≥ r + 1` by `t + 3Δ`, then by
round monotonicity it must pass through round `r + 1` at some
intermediate step.

### T1, T2, T3, T4 — stand as stated

T1 (Block Availability), T2 (Causal Availability), T3 (Round
Progression), and T4 (Round Termination) all hold under
`BelugaPartialSynchrony` as currently stated in the paper. We
recommend **dropping** the paper's separate "Eventual*" hypotheses
that the §5 prose mentions for T2 and T4: they are derivable from
items 5 and 6 of `BelugaPartialSynchrony` (per-action liveness +
universal in-pool delivery).

## 3. Suggested proof sketches

Each sketch below has roughly the length of the paper's existing
proof and uses paper notation throughout.

### L1 (round entry within 3Δ) — proof sketch

Let `v_w` be the witness honest validator at round `r` at time
`t`. By Assumption 2 item 3 (round-advance liveness), `v_w`
advances to round `r + 1` by some time `t_1 ≤ t + Δ`, and to
round `r + 2` by some `t_2 ≤ t + 2Δ`.

By item 4 (protocol synchronization), at time `t_2` every honest
validator's round is within one of `v_w`'s round; so every honest
validator is at round `≥ r + 1`.

If `t_2 ≤ t + 2Δ`, take `t' = t_2`. If `t_2` falls within
`(t + 2Δ, t + 3Δ]`, the bound still holds. □

### L2 (round-to-round latency ≤ 3Δ) — proof sketch

Apply L1 to the witness validator `v` at round `r`, time `t`. We
get `t' ≤ t + 3Δ` at which `v` is at round `≥ r + 1`. Since `v`'s
round increases by at most one per protocol step (each `advance`
adds 1) and is non-decreasing, there is some intermediate time
`t'' ∈ [t, t']` at which `v`'s round equals exactly `r + 1`. □

### T1 (Block Availability) — proof sketch

This proof uses the action-priority structure of §4 directly and
does not need the ImPoA argument the paper currently sketches.

Suppose validator `v_i` (honest) has accepted block digest `d` at
time `t`. We must show that `v_i` eventually emits
`block_store_i(B, d)` for some block `B`.

Choose any post-GST time `t_0 ≥ max(t, GST)`. By items 3 and 4 of
Assumption 2, every honest validator (including `v_i`) advances
infinitely often after `t_0`. Consider the **next** advance step
of `v_i` after `t_0`. The §4 protocol's action priority puts
`store` strictly above `advance`: a validator can only advance
when no `store` action is enabled. Hence at the moment `v_i`
advances, every digest in `v_i`'s accepted set whose corresponding
block is in the pool must already be stored.

Block `d`'s corresponding block `B` is in the pool at time `t`
(since `v_i` accepted it). By the protocol's pool monotonicity,
`B` remains in the pool. Therefore at the advance step, `B`'s
digest is already stored — `v_i` has emitted `block_store_i`. □

**Why this sketch does not need ImPoA.** The paper's current T1
proof routes through ImPoA: "the parent blocks are referenced by
`f + 1` subsequent blocks → at least one honest validator stored
them → the validator pulls them → the validator eventually
accepts them, then stores them." This argument is needed if T1
is read as "even when a validator is missing some parents at the
moment of acceptance, it will eventually catch up", because then
the catch-up step has to be justified — and ImPoA + pull is the
mechanism §4.3 supplies for that.

The sketch above does not need this catch-up step because it
relies only on the *action-priority order* of §4 (`accept ≻
store ≻ advance`, all above `propose`). The argument is
structural rather than temporal: at the moment `v_i` advances —
which it does within `Δ` of becoming able to, by per-action
liveness — every accepted-and-still-in-pool digest is *already*
stored, because otherwise the higher-priority `store` action
would have fired first instead of the `advance`. No pull, no
ImPoA, no f+1-references quorum is consulted; the conclusion is
forced by the priority order alone.

ImPoA is still required for the *runtime* of the protocol: it is
what enables a validator to *accept* a block whose parents it has
not directly received, by trusting the f+1-reference quorum
instead. T1 is downstream of the accept rule and does not need to
re-derive what made acceptance valid in the first place — once
`v_i` has accepted `d`, the structural action-priority argument
takes over.

### T2 (Causal Availability) — proof sketch

Suppose `v_i` (honest) has accepted block `B` at time `t`, and
`B'` is a causal ancestor of `B` (`B' ∈ causal(B)`). We must show
`v_i` eventually accepts `B'`.

Induction on the length of the causal-ancestor chain `B → B'`.

- **Length 0** (`B' = B`). `v_i` has already accepted `B`. Done.
- **Length n + 1** (`B' = parent(M)` for some intermediate `M`
  with `B → M` of length n). By IH, `v_i` eventually accepts
  `M` at some time `t_M ≥ t`. The block `B'` is a parent of `M`,
  so `B' ∈ pool` at time `t` (the parents of any in-pool block
  are in the pool). By Assumption 2 item 6 (universal in-pool
  delivery), there is a time `t' ≥ t_M` at which the
  `block_propose` op for `B'` is in `v_i`'s inbox. By item 5
  (accept-action liveness), `v_i` accepts `B'` within `Δ` of `t'`.
  □

**Why this sketch does not need a separate ImPoA / f+1-references
argument.** The paper's current T2 proof folds two things into
one: (i) the recursion through causal ancestors, and (ii) the
liveness step that says each ancestor will eventually be received.
For (ii), the paper invokes ImPoA + f+1-references + the pull
mechanism inline.

In the sketch above, (i) and (ii) are separated. (i) is just the
length-induction over `Reaches`, with no protocol content. (ii)
is item 6 of `BelugaPartialSynchrony` — "every block in the pool
is eventually received" — which is exactly the conclusion ImPoA +
the pull mechanism are designed to deliver. By naming the
conclusion as a stated assumption, the paper does not need to
re-derive it inside T2: T2 just cites it, and the structural
recursion is the entire content of the proof.

The atomic §4.3 derivation (every f+1-referenced block is pulled
within `2Δ` after the witness honest references it) is still
where item 6 *comes from*; making it explicit lets §5's prose
treat the conclusion as a black box.

## ImPoA: where it is used and where it is not

It is worth being precise about what ImPoA buys. The accept rule
of §4.3 reads "an honest validator may accept a block `B` whose
parents have *all* been observed — either explicitly accepted, or
implicitly available because `f + 1` subsequent in-pool blocks
reference them." The ImPoA disjunct (the "implicit availability"
half) is what lets a validator accept without having directly
received every parent.

This makes ImPoA *load-bearing for the runtime of the protocol*:
without it, an honest validator that hasn't received a parent via
push, and isn't fast enough to issue a pull request before the
round timeout fires, would be stuck. With it, the f+1-reference
quorum gives the validator structural permission to accept.

ImPoA is **not** load-bearing for the §5 *correctness* proofs:

- **T1** (Block Availability) is structural in the action-priority
  order, downstream of the accept rule: it says "if you've
  accepted, you'll store before advancing", regardless of *how*
  you accepted.
- **T2** (Causal Availability) recurses on `Reaches` and at each
  step uses item 6 (universal in-pool delivery) to argue the
  ancestor is received. The ancestor is then accepted via the
  `received` disjunct of the accept rule, not the ImPoA disjunct.
- **T3** (Round Progression) uses the propose-before-advance
  gate and round liveness — no acceptance argument at all.
- **T4** (Round Termination) again accepts via `received`, not
  via ImPoA, once item 6 lands the block in the inbox.

So the §5 proofs can be read as:
**ImPoA + pull mechanism ⟹ item 6 (universal in-pool delivery)
⟹ T1 / T2 / T3 / T4** — without §5 needing to look inside the
arrow. This separation simplifies the §5 prose substantially and
matches the formalization, which similarly never opens the ImPoA
disjunct in any §5 proof.

### T3 (Round Progression) — proof sketch

For any round `r`, we must show that some honest validator
eventually emits at least `2f + 1` distinct `block_propose_i(B, r)`
ops with distinct authors.

By item 3 of Assumption 2, every honest validator eventually
reaches round `r + 1`. Combine with L1: for some post-GST time
`t_r`, every honest validator is at round `≥ r + 1` by `t_r`.
Each honest validator that reached round `r + 1` must have first
proposed for round `r` (by §4's propose-before-advance priority).

By Assumption (`n ≥ 3f + 1`, with at most `f` Byzantine), there
are at least `2f + 1` honest validators. Each contributes a
distinct `block_propose_i(B, r)` to the operation log by `t_r`.
□

### T4 (Round Termination) — proof sketch

For any round `r` and honest validator `v`, we must show that `v`
eventually accepts `2f + 1` distinct authors' round-`r` blocks.

By T3, by some time `t_r`, at least `2f + 1` honest validators
have proposed for round `r`. Each such proposal places a block in
the global pool whose author is the proposing validator.

By Assumption 2 item 6 (universal in-pool delivery), each of these
`2f + 1` blocks is eventually known to `v`'s inbox. By item 5
(accept-action liveness), `v` accepts each of them within `Δ`.
Combining (and using the digest-determinism of §2.1 to argue
distinct authors yield distinct accepted digests), `v` has
accepted blocks from `2f + 1` distinct authors. □

## 4. Optional §4 changes

The §5 sketches above are independent of these, but adopting them
would simplify the §5 prose further.

### 4a. State the §4.3 conclusion

§4.3 currently describes the pull mechanism (`pullCandidate`,
issue, response, delivery) but never names the conclusion. We
recommend adding, at the end of §4.3:

> **Pull conclusion.** Combined with the §2 push delivery, the
> pull mechanism establishes that every block in the global pool
> is eventually known to every honest validator post-GST.

Then item 6 of `BelugaPartialSynchrony` simply cites §4.3 by name.

### 4b. Make accept/store atomicity explicit (or split with priority)

§4 prose treats `block_accept` and `block_store` as conceptually
distinct outputs (consumed at different layers — consensus reads
`accept`, execution reads `store`). Figure 8 in Appendix E,
however, glues them into a single `create_new_block` step. This
ambiguity affects T1: under atomic accept-and-store, T1's
conclusion holds at the moment of acceptance; under split actions,
T1 needs the action-priority argument from §3 above.

We recommend either (a) collapsing accept and store into a single
`block_accept_and_store` action in Figure 8 (T1's proof becomes
one sentence), or (b) keeping them split and explicitly stating
the §4.2 action priority "`accept ≻ store ≻ advance`" so T1's
proof can cite it. Option (b) matches the formalization.

### 4c. Block-digest determinism

§2.1 presents `B.d` as a primitive field of the block alongside
`B.r`, `B.author`, etc. Every uniqueness argument in §4.4 and
§D.3 silently relies on the digest being a *function of `(B.r,
B.author, …)`*. We recommend either:

1. Defining `B.d := digest(B.r, B.author, B.parents, B.payload, …)`
   in §2.1 — the cleanest restatement.
2. Stating block-digest determinism as a named property alongside
   Definition 1: "*for any two blocks `B_1, B_2` in the pool,
   `B_1.d = B_2.d` iff `B_1 = B_2`.*"

In implementations the property comes for free (digests are
cryptographic hashes of contents); a formal statement of the
protocol that does not state it is missing a load-bearing fact.

## What cannot be proved without further changes

The following are facts the paper currently asserts that we have
**not** proved, and for which mechanization suggests the paper
either weaken the claim or add hypotheses.

- **L1 strict same-round form.** Not provable from the cited
  assumptions for the reason given in §2 above. We recommend the
  lockstep-progress restatement.

- **T7 (consensus safety) as currently stated.** T7's prose proof
  conflates two ingredients: (a) "consistent views" (paper L16's
  conclusion) is *not* equivalent to "identical views" — bridging
  the two requires a *liveness* premise (decision completeness),
  which is a §D.2 result, not a §D.3 safety result; and (b) the
  paper's "transaction ordering respects view equality" treats
  `order` as separable from `view` when in fact `order` is
  *computed* from `view`. We recommend either (1) restating T7's
  conclusion to prefix-consistency on the *intersection of decided
  positions* (which is what atomic-broadcast safety actually means
  and what L16 alone delivers), or (2) explicitly importing
  decision completeness as a named premise of T7 with a citation
  to Theorem 6 / §D.2 for its discharge, or (3) defining `order`
  as a function of `view` in §D.3 so the "respects view equality"
  step becomes trivial.

- **Probabilistic latency bounds (Theorem 5, Lemmas 6 and 7).**
  These require a probability framework which is out of scope for
  the current formalization.
