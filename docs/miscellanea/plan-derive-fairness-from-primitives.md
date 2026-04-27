# Plan: deliver §5 from paper primitives, without `SchedulerFairness`

> **Goal.** Replace the axiomatic `SchedulerFairness` assumption in
> the §5 mechanization with a *theorem* derived from the paper's
> stated primitives: `Δ`-delivery (paper §2), the per-round timeout
> `T_rd = 4Δ` (paper §4.2), the push protocol (paper §4.2), and
> ImPoA (paper §4.3). When this plan completes, every §5 theorem
> (L1, L2, T1, T3, T4 — and `belugaTrace_isBlockSynchronizer`)
> takes only paper-stated assumptions.

> **Companion to**
> [`paper-feedback-impoa-vs-fairness.md`](paper-feedback-impoa-vs-fairness.md),
> which establishes that `SchedulerFairness` *can* be derived from
> these primitives but the current trace model abstracts the
> primitives away. This doc lays out the model refinement.

## End state

Before:
```
theorem theorem3_round_progression
    (system : ...) (hids : ...) (time : TimeMap) (h_time : ...)
    (h_sync : PartiallySynchronous ...)
    (h_fair : SchedulerFairness system time)   -- <-- AXIOM
    ... :
    RoundProgression system (belugaTrace system) := ...
```

After:
```
theorem theorem3_round_progression
    (system : ...) (hids : ...) (time : TimeMap) (h_time : ...)
    (h_sync : PartiallySynchronous ...)
    (h_delivery : NetworkDelivery system time)  -- <-- Δ-bounded delivery (paper §2)
    ... :
    RoundProgression system (belugaTrace system) := ...
```

Where `NetworkDelivery` is the only new axiom and it is the paper's
literal §2 statement: "post-GST, every honest-to-honest message
arrives within Δ of being sent."

`SchedulerFairness` becomes:
```
theorem schedulerFairness_holds
    (system : ...) (hids : ...) (time : TimeMap) (h_time : ...)
    (h_delivery : NetworkDelivery system time)
    ... :
    SchedulerFairness system time := ...
```

— derived from the network model + push protocol + timeout + ImPoA.

## Phasing overview

| Phase | Scope | Effort | Depends on |
|-------|-------|--------|------------|
| A | Per-validator time tracking | ~3 days | — |
| B | In-flight messages + delivery | ~5 days | A |
| C | `T_rd = 4Δ` timeout branch | ~3 days | A |
| D | ImPoA-based accept rule | ~5 days | B |
| E | Derive `schedulerFairness_holds` | ~7 days | A–D |
| F | Migrate §5 wrappers | ~2 days | E |

**Total: ~3.5–4 weeks of full-time mechanization.**

## Phase A — Per-validator time tracking

**Why.** The timeout `T_rd = 4Δ` fires per validator on its local
clock since entering the current round. Without per-validator
time, we can't model the timeout.

**Code changes.**

1. Extend `BelugaValidator` (in `Beluga/State.lean`):
   ```
   structure BelugaValidator where
     ...
     currentRound : Round := 0
     roundEntryTime : Nat := 0   -- NEW: wall-clock at last round entry
     ...
   ```

2. Threading `roundEntryTime` through `step`. The signature of
   `step` changes from `step (system) (s) : BelugaState` to
   `step (system) (s) (currentTime : Nat) : BelugaState` so that
   `doAdvance` can record `roundEntryTime := currentTime` for the
   advancing validator.

3. Update `belugaTrace`: takes the `time : TimeMap` as a
   parameter, calls `step system (belugaTrace n) (time n)` at
   each step.

   ```
   def belugaTrace (system) (time : TimeMap) : Trace BelugaState :=
     fun n => Nat.rec (BelugaState.init system) (fun i s => step system s (time i)) n
   ```

   This is a structural change — `belugaTrace` is no longer a
   function of system alone. Every theorem that uses it needs an
   extra `time` argument (most already pass `time` separately, so
   the impact is limited; some helpers will need their signatures
   tweaked).

**Deliverable.** `step`, `belugaTrace` extended; per-validator
`roundEntryTime` updated by `doAdvance`. Build clean.

**Risk.** Threading `time` through every helper that mentions
`belugaTrace` is mechanical but tedious. Estimate: ~50 signature
updates across the codebase.

## Phase B — In-flight messages + delivery

**Why.** The paper's push protocol works by validators
broadcasting their proposed blocks. Other validators receive
them within `Δ` post-GST. Acceptance is conditioned on having
*received* the block.

**Code changes.**

1. New type `Beluga/Network.lean`:
   ```
   structure DeliveryEvent where
     sender : ValidatorId
     recipient : ValidatorId
     op : ValidatorOperation       -- the message body
     deliveryTime : Nat            -- wall-clock when it arrives
     deriving Repr, DecidableEq
   ```

2. Extend `BelugaState`:
   ```
   structure BelugaState where
     ...
     inflight : List DeliveryEvent := []     -- NEW: pending deliveries
     received : ValidatorId → List ValidatorOperation := fun _ => []
                                              -- NEW: per-vid received messages
   ```

3. Modify `step` to first deliver pending messages (`inflight`
   events with `deliveryTime ≤ currentTime`) into the recipient's
   `received` list, then run `tryActFor`.

4. Modify `doPropose` to *broadcast*: append `DeliveryEvent`s for
   every other validator with `deliveryTime ∈ [currentTime,
   currentTime + Δ]` (post-GST) or unbounded (pre-GST).

   For Byzantine senders, the deliveryTime is unconstrained
   (modeling adversarial scheduling).

5. Modify the accept rule in `tryActFor`:
   ```
   accept B only if B ∈ received[vid]  AND  parents accepted (or ImPoA)
   ```

6. New axiom `NetworkDelivery`:
   ```
   def NetworkDelivery (system : BlockSynchroniserSystem) (time : TimeMap) : Prop :=
     ∀ k vid_s vid_r op, vid_s honest → vid_r honest →
       time k ≥ system.GST →
       op ∈ (belugaTrace ... k).emittedOperations →
       op was emitted by vid_s →
       ∃ k', k ≤ k' ∧ time k' ≤ time k + system.Δ ∧
         op ∈ ((belugaTrace ... k').received vid_r)
   ```

**Deliverable.** Network state in `BelugaState`; `step` processes
deliveries; `doPropose` schedules deliveries; accept rule
conditions on `received`. Sufficient `NetworkDelivery`-axiom
proofs for the simple case (no Byzantine, all delivered). Build
clean.

**Risk.** Modeling Byzantine senders is subtle. The paper
hand-waves "Byzantine validators may delay their messages
arbitrarily". We need to encode that as: Byzantine senders'
DeliveryEvents have arbitrary `deliveryTime`, while honest
senders' have `deliveryTime ≤ currentTime + Δ` post-GST.

## Phase C — `T_rd = 4Δ` timeout branch

**Why.** The paper's actual liveness mechanism. Without this,
honest validators can be stuck waiting for blocks that never
arrive (Byzantine senders), and round progress fails.

**Code changes.**

1. Add `T_rd` to `BlockSynchroniserSystem` (or define as `4 * Δ`):
   ```
   structure BlockSynchroniserSystem where
     ...
     /-- Per-round timeout (paper §4.2). Set to `4Δ`. -/
     T_rd : Nat := 4 * Δ   -- or as a structure field for flexibility
   ```

2. Modify `tryActFor`'s advance branch:
   ```
   -- 4. Advance round if everyone proposed OR timeout expired
   if allProposedFor system s r OR currentTime ≥ bv.roundEntryTime + system.T_rd then
     some (doAdvance s vid currentTime)
   else none
   ```

3. The timeout uses the per-validator `roundEntryTime` from Phase A
   and `currentTime` from the `step`'s parameter.

**Deliverable.** Timeout branch in `tryActFor`; `doAdvance`
updates `roundEntryTime := currentTime`. Build clean.

**Risk.** The new advance branch breaks existing proofs of
`step_advance_inversion`, `step_advance_implies_*`. These were
predicated on `allProposedFor`; now we have a disjunction. Roughly
double the case analysis depth. Estimate: ~150 lines of
re-proving.

## Phase D — ImPoA-based accept rule

**Why.** Strengthens the accept rule to allow accepting B without
direct parent-acceptance, as long as B has f+1 in-pool
referencers (paper §4.3 implicit availability). This is what
allows the network to make progress when not all blocks are
directly delivered.

**Code changes.**

1. Define `implicitlyAvailable (s : BelugaState) (B : Block) (f : Nat) : Bool`:
   ```
   def implicitlyAvailable (s : BelugaState) (B : Block) (f : Nat) : Bool :=
     (s.blocks.filter (fun B' => B.d ∈ B'.parents)).length ≥ f + 1
   ```

2. Modify accept rule:
   ```
   match s.blocks.find? (fun B =>
       B ∈ received[vid] AND
       !hasAcceptedDigest s vid B.d AND
       (B.parents.all (fun pd => hasAcceptedDigest s vid pd) OR
        ∀ pd ∈ B.parents, implicitlyAvailable s (block_with_digest pd) system.f)) with
   ```

3. Update T2's proof — currently relies on `acceptedParents`
   invariant (vid accepts B → vid accepts all parents). Under
   ImPoA accept, this invariant fails (vid can accept B with
   parents only implicitly available, not accepted). T2's
   `causallyClosed_trace` invariant needs to be reworked:
   "vid accepts B → for every B' in causal(B), B' is *available*
   to vid (either accepted or implicitly available)". The
   `Eventually` quantifier in `CausalAvailability` then becomes
   non-trivial — need a future step at which the implicitly
   available B' is pulled and accepted.

4. Add a "pull" mechanism: when vid wants to verify ImPoA, it
   issues a pull request; eventually the block arrives. Pull
   correctness depends on f+1 references → at least 1 honest
   referencer → that honest validator stored B → can serve the
   pull.

**Deliverable.** ImPoA accept rule active; T2 reworked to use
ImPoA-aware causal-availability invariant. Build clean.

**Risk.** This is the highest-risk phase. The accept rule change
ripples through every proof that uses `hasAcceptedDigest` (T1,
T3, T4 included). The ImPoA path requires a richer pool-to-pull
correspondence. Estimate: 5-7 days, possibly more.

**Mitigation.** Stage this phase incrementally: first add the
ImPoA branch as an *alternative* (validator can use either
direct or ImPoA path); existing proofs still work via the direct
path. Then later strengthen if needed.

## Phase E — Derive `schedulerFairness_holds`

**Why.** This is the payoff. Prove that for `belugaTrace`
constructed with the network + timeout + ImPoA model,
`SchedulerFairness` holds.

**Proof structure** (matches paper L1):

```
theorem schedulerFairness_holds
    (system : BlockSynchroniserSystem) (hids : ValidIds system)
    (time : TimeMap) (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system time) time)
    (h_delivery : NetworkDelivery system time)
    -- (Other paper-stated assumptions: 2f+1 honest, validator IDs, etc.
    --  These are now structure fields after the F-1/F-13 refactor.)
    : SchedulerFairness system time := by
  intro k r h_post_gst ⟨vid_w, bv_w, h_w_honest, h_w_get, h_w_round⟩
  -- 1. Within Δ post-k, every honest receives vid_w's round-r block
  --    (h_delivery applied to vid_w's round-r propose op).
  -- 2. Within 2Δ post-k, every honest's accept queue contains enough
  --    round-r blocks to make progress (via direct or ImPoA path).
  -- 3. By 4Δ post-each-validator's-roundEntry, the timeout fires
  --    even if 2f+1-honest-accepts didn't materialize.
  -- 4. Hence by 3Δ post-k, every honest is at round ≥ r + 1.
  ...
```

The proof is essentially paper L1 mechanized. Each step needs:
- Lemmas about `step`'s message-processing semantics.
- Lemmas about `doPropose`'s broadcast scheduling.
- The timeout fire condition.
- ImPoA-availability → pull-recovery → accept.

**Deliverable.** `schedulerFairness_holds` proved. The §5
mechanization can now be re-routed to take `NetworkDelivery`
instead of `SchedulerFairness`.

**Risk.** This is the largest phase. The argument has 4-5
sub-claims, each with its own helper lemmas. Estimate: 5-7 days,
~600-1000 lines of Lean.

## Phase F — Migrate §5 wrappers

**Why.** Update L1, L2, T1, T3, T4 to take `NetworkDelivery`
directly, deriving `SchedulerFairness` internally.

**Code changes.**

1. Replace `(h_fair : SchedulerFairness ...)` parameter with
   `(h_delivery : NetworkDelivery ...)` in:
   - `belugaTrace_satisfies_post_gst_liveness`
   - `lemma1_honest_round_entry`
   - `lemma2_round_latency`
   - `theorem1_block_availability`
   - `theorem3_round_progression`
   - `theorem4_round_termination`
   - `belugaTrace_isBlockSynchronizer`

2. Inside each, derive `SchedulerFairness` via
   `schedulerFairness_holds` and pass to existing proof.

3. Optional: drop `SchedulerFairness` as a public def entirely;
   keep it as `private def` used internally.

**Deliverable.** All §5 theorems take only paper-stated
assumptions. F-1 in `mechanization-findings.md` updated to note
the assumption is now derived.

**Risk.** Mostly mechanical. ~2 days.

## Cross-cutting concerns

### Backward compatibility

During phases A–E, existing `belugaTrace_*` proofs may break
when their helpers' signatures change. Strategy:
- Each phase preserves the build by rebasing existing proofs
  onto the new signatures. No long broken-build periods.
- Branch off `master` at the start; merge back when each phase
  passes.

### Validation.lean (`goldenSystem`)

The 4-validator demo trace will need to provide:
- An initial `time` map (e.g., step-equals-time).
- Initial `inflight` and `received` (empty).
- `T_rd` field in the system (default 4Δ).
- Concrete `NetworkDelivery` proof (trivial since all 4 are honest).

The reachability + counterexample lemmas in Validation.lean
should still go through, but each takes ~1 fix.

### Mysticeti (D.2)

The Mysticeti liveness lemmas (L8, L11, etc.) currently have a
`Mysticeti/Liveness.lean` that takes its own bundle. They depend
on Beluga's L1/L2 transitively. They will benefit automatically
from the §5 migration — no extra work.

### Aristotle delegation

Each phase has clear hand-proof targets that don't require
Aristotle. Phase D and Phase E may benefit from delegation when
specific lemmas hit Mathlib lookup walls. Plan: hand-prove first,
delegate only the remaining gaps.

## Open questions (worth resolving before starting)

1. **Should `time` become a parameter of `belugaTrace`, or stay
   external?** Current state: external. Phase A pushes for making
   it internal. Implication: trace becomes
   `Trace (BelugaState × Nat)` or similar. ~50 signature changes.

2. **Byzantine sender modeling.** Paper says Byzantine senders may
   delay arbitrarily. In our model, do we encode this as
   non-deterministic `deliveryTime`, or as an oracle? Recommend:
   non-deterministic, with `Δ` bound only for honest-honest pairs.

3. **Per-round timeout vs. per-action timeout.** Paper has T_rd
   per-round. Some prose suggests per-action behavior too. Recommend:
   T_rd per-round only; per-action progress comes from delivery +
   accept rule.

4. **Pull mechanism explicit?** Phase D's ImPoA accept needs pull
   to work. Do we model the pull request/response explicitly, or
   abstract via "ImPoA-available → eventually delivered"? Recommend:
   abstract for the first pass; explicit pull is a refinement.

## Decision needed

Two go/no-go decisions before starting:

1. **Scope.** Is the ~4-week effort worthwhile for paper
   faithfulness? Alternatives:
   - **(a)** Document the abstraction (already done — current
     state). `SchedulerFairness` stays as an axiom, clearly
     explained. No further work.
   - **(b)** Phase A + Phase C only (~6 days). Add per-validator
     time + timeout, but keep the network model abstract. Modest
     refinement; `SchedulerFairness` still axiom but framed in
     timeout terms.
   - **(c)** Full Phases A–F. ~4 weeks. Paper-faithful end state.

2. **Branching strategy.** If we proceed with (c), branch
   `feature/derive-fairness` off master, work in chunks committed
   to that branch, merge when E completes. Each phase a separate
   commit on the branch.

If decision is (c), suggested kick-off: Phase A this week, with a
checkpoint after A completes (to validate the threading approach
before doing more).
