# Resume notes — finishing Mysticeti §D.2

## State at last commit (`0f08a86`)

The structural refactor is complete. All §D.2 theorems are now
direct theorems against `networkBelugaTraceWithPull`, taking
`MysticetiBelugaSynchrony` plus standard BFT side conditions.
Two of eight liveness obligations are fully discharged from first
principles; six remain with `sorry` placeholders.

### Bundle (`MysticetiBelugaSynchrony`)

```lean
structure MysticetiBelugaSynchrony (system) (time) : Prop
    extends Beluga.Network.BelugaWithPullFairness system time where
  proposeScheduling : ProposeSchedulingWithPull system time   -- §4.2
  storeScheduling   : StoreSchedulingWithPull   system time   -- §4.2
  leader_inclusion  : ...                                       -- §D.1.2
  cert_pattern_at_r2 : ...                                      -- §D.1.1
```

All four added fields are paper-stated rules, not paper-derived
theorems. The bundle structure mirrors `BelugaWithPullFairness`'s
extension pattern.

### Discharged

- **`honest_round_entry`** — directly via
  `Beluga.Network.lemma1_honest_round_entry`.
- **`leader_propose`** — by composing L1 (4Δ catch-up) with
  `proposeScheduling` (Δ propose-action) and the round-monotone
  propose-witnessing invariant
  `network_proposed_for_lt_currentRoundWithPull`. Case-split on
  whether the leader has already passed round `r`.

### Pending (sorries, in order of complexity)

1. **`honest_ref_leader`** (paper §D.2 L7).
   Skeleton:
   - Apply `leader_propose` → `B_L` at step `k₁`.
   - Apply `Beluga.Network.network_all_honest_eventually_at_roundWithPull`
     with `R = r + 2` → `vid_referencer` is at round ≥ `r + 2` at
     step `k₂`.
   - Apply `network_proposed_for_lt_currentRoundWithPull` at `k₂`
     for round `r + 1` → `hasProposedFor vid_referencer (r + 1)`.
   - Extract `B_ref` via
     `hasProposedFor_implies_propose_op` and the propose-op invariant
     `network_propose_op_invariant_traceWithPull`.
   - Show `B_L` persists in the pool from `k₁` to the relevant later
     step (blocks-monotonicity for `networkBelugaTraceWithPull` —
     not yet a direct lemma in Beluga/Network.lean; the pattern is
     mirrored from `belugaTrace_blocks_monotone`).
   - Show `vid_referencer` has accepted `B_L.d` by the relevant
     step. By `inPoolDelivery` (from `BelugaPartialSynchrony`)
     followed by `acceptScheduling`.
   - Apply `leader_inclusion` (the bundle primitive) →
     `B_L.d ∈ B_ref.parents`.

2. **`honest_certify_leader`** (paper §D.2 L8).
   - Apply `honest_ref_leader` for each honest `vid_ref` (there are
     `≥ 2f + 1` of them).
   - Each honest's round-`(r + 1)` block has `B_L` as parent → `B_L`
     has `≥ 2f + 1` distinct-author strong-referencers → `certified
     system state B_L`.
   - Mechanically: iterate over the honest validator list, accumulate
     the strong-referencer set, apply `certificatePattern`'s
     definition (`(strongReferencerAuthors state B).length > 2 *
     system.f`).

3. **`three_consec_commit`** (paper §D.2 Lemma 9 corollary).
   - By `lemma10_round_robin_pigeonhole`, find `r₁ ≥ startRound`
     with leaders at `r₁`, `r₁ + 1`, `r₁ + 2` all honest.
   - Apply `honest_certify_leader` for each round → leader at each
     round is `certified`.
   - Apply `cert_pattern_at_r2` (bundle primitive) →
     `certificatePatternAtB system state B_L (B_L.r + 2)` for each.
   - Unfold `directDecide`'s definition: when
     `certificatePatternAtB ... (B.r + 2)` holds, `directDecide`
     returns `Decision.ToCommit`.

4. **`backward_induction`** (paper §D.2 Lemma 11 backward step).
   - Backward induction on rounds from `r₁` down to `r`.
   - Use `lemma14_no_skip` (no skip when committed, paper L14) +
     `lemma15_unique_cert` (unique cert per round, paper L15) +
     `lemma13_cert_persistence` (paper L13) + the `indirectDecide`
     rule definition.
   - Each undecided leader at an earlier round becomes `ToCommit`
     or `ToSkip` via the indirect rule, never `Undecided`.
   - The structural lemmas L13/L14/L15 are already proved in
     `Mysticeti/Safety.lean`.

5. **`lemma12_referenced_accepted`** (paper §D.2 L12).
   - From the `f + 1`-honest-references precondition: each honest's
     block has `d` as parent.
   - Use the structural protocol fact that an honest validator's
     block has only accepted parents (admission control: `acParentSelection`
     filters to `filterAcceptable` parents). So each of the `f + 1`
     honest validators has accepted `d`.
   - Hence `B_d` (the block with digest `d`) is in the pool of at
     least one honest validator's accepted set, so it is in
     `(networkTraceWithPull system time k₀).base.blocks`.
   - Apply `inPoolDelivery` to get `B_d` delivered to `vid`.
   - Apply `acceptScheduling` to get `vid` to accept.
   - The "honest's block has only accepted parents" link may need
     a small structural lemma (similar in spirit to `BlockInv` /
     `AcceptInv` from `Beluga.Protocol`); a candidate scaffold is
     in the existing `at_least_f_plus_one_honest_referencers` proof
     (now removed from this file).

6. **`theorem6_consensus_liveness`** (paper §D.2 Theorem 6).
   - Compose `lemma11_eventual_decision` (every leader eventually
     decided) + `lemma12_referenced_accepted` (every committed
     leader's referenced blocks eventually accepted).
   - `vid_acc` has accepted `B` → by Beluga T2-form acceptance
     propagation (similar to a §5 T2 wrapper), every honest
     `vid_h` eventually accepts `B`.
   - `B`'s payload appears in `vid_h`'s canonical transaction
     order via `Beluga.accepted_implies_in_belugaTransactionOrder`
     (already proved); use the state-level
     `belugaTransactionOrderState` for the network-aware trace.

## Auxiliary lemma needed

**Blocks-monotonicity for `networkBelugaTraceWithPull`** — analogous
to `belugaTrace_blocks_monotone` (now removed). Statement: for any
`i ≤ j` and `B ∈ (networkTraceWithPull system time i).base.blocks`,
`B ∈ (networkTraceWithPull system time j).base.blocks`. Proof
mirrors the synchronous version using
`networkStepWithPull_emittedOperations_monotone` and the structural
`networkStepWithPull` body. Place it near the top of
`Mysticeti/Liveness.lean` (no Beluga/ edits needed — write it as
a private helper).

## Build state

`lake build` succeeds. 6 `declaration uses sorry` warnings, all in
the §D.2 theorem bodies listed above. No axioms, no
stronger-than-paper assumptions; the bundle's primitives are paper
§4.2/§D.1 protocol rules.
