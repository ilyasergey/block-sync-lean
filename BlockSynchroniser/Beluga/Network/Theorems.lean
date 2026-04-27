/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Beluga §5 main theorems against `networkTrace` — the migration target
of the §5-on-networkTrace work documented in
[`docs/migration-network-trace.md`](../../../docs/migration-network-trace.md).

Each theorem here mirrors a §5 paper claim, but the conclusion is
about `networkTrace.base` (the network-aware trace's projected
state), and the proof routes through `Network.schedulerFairness_holds`
(the proved fairness theorem) plus structural invariants of
`networkTrace`.

Phase 5 of the migration is to populate this file with the full
§5 bundle. Currently populated: L1 (round entry) and L2 (round
latency). T1 / T2 / T3 / T4 are queued pending the trace-level
invariant migration (BlockInv / AcceptInv / CausallyClosed) and the
deeper helpers (`find_advance_step`, `accepted_at_advance`, etc.).
-/
import BlockSynchroniser.Beluga.Network.Fairness
import BlockSynchroniser.Properties

namespace BlockSynchroniser
namespace Beluga
namespace Network

/-! ## §5 Lemma 1 (network-trace) — round entry within 3Δ -/

/-- **Lemma 1 (paper §5).** Network-trace formulation: after GST,
given an honest validator at round `r`, every honest validator
reaches round `≥ r + 1` within `3Δ`. Direct one-line consequence
of `schedulerFairness_holds`. -/
theorem network_lemma1_honest_round_entry
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_prim : PartiallySynchronousFairness system time) :
    ∀ vid_ref r k₀, isHonestValidator system vid_ref = true →
      time k₀ ≥ system.GST →
      (∃ bv_ref, (networkTrace system time k₀).base.getValidator vid_ref = some bv_ref ∧
        bv_ref.currentRound = r) →
      ∃ k', k₀ ≤ k' ∧ time k' ≤ time k₀ + 3 * system.Δ ∧
        ∀ vid, isHonestValidator system vid = true →
          ∃ bv, (networkTrace system time k').base.getValidator vid = some bv ∧
                bv.currentRound ≥ r + 1 := by
  intro vid_ref r k₀ h_honest h_post_gst ⟨bv_ref, h_bv_ref, h_round⟩
  have h_persistent : ∀ vid k, isHonestValidator system vid = true →
      ∃ bv, (networkTrace system time k).base.getValidator vid = some bv :=
    fun vid k h => network_honest_validator_persistent_trace system time vid h k
  exact schedulerFairness_holds system time h_mono
    h_prim.networkDelivery h_prim.actionScheduling h_prim.boundedRoundSpread
    h_persistent
    k₀ r h_post_gst ⟨vid_ref, bv_ref, h_honest, h_bv_ref, h_round⟩

/-! ## §5 Lemma 2 (network-trace) — round-to-round latency ≤ 3Δ -/

/-- **Lemma 2 (paper §5).** Network-trace formulation: after GST,
given an honest validator `vid` at round `r`, by some step within
`3Δ`, `vid` is at round exactly `r + 1`. Uses
`schedulerFairness_holds` to bring `vid` to `≥ r + 1`, then applies
`network_round_intermediate_value` to extract the exact-`r+1` step. -/
theorem network_lemma2_round_latency
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_prim : PartiallySynchronousFairness system time) :
    ∀ vid r k,
      isHonestValidator system vid = true →
      time k ≥ system.GST →
      (∃ bv, (networkTrace system time k).base.getValidator vid = some bv ∧
        bv.currentRound = r) →
      ∃ k' ≥ k, time k' ≤ time k + 3 * system.Δ ∧
        ∃ bv, (networkTrace system time k').base.getValidator vid = some bv ∧
              bv.currentRound = r + 1 := by
  intro vid r k h_honest h_post_gst ⟨bv, h_bv, h_round⟩
  -- Apply network_lemma1_honest_round_entry to get all honest at ≥ r + 1.
  obtain ⟨k', hk'le, hk'time, hk'all⟩ :=
    network_lemma1_honest_round_entry system time h_mono h_prim
      vid r k h_honest h_post_gst ⟨bv, h_bv, h_round⟩
  obtain ⟨bv', hbv', hbv'rnd⟩ := hk'all vid h_honest
  -- Apply intermediate value to get an exact-r+1 step in [k, k'].
  have hle_r : bv.currentRound ≤ r + 1 := by rw [h_round]; exact Nat.le_succ r
  obtain ⟨kc, hkc_lo, hkc_hi, bvc, hbvc, hrnd_eq⟩ :=
    network_round_intermediate_value system time vid k k' (r + 1) hk'le bv bv' h_bv hbv'
      hle_r hbv'rnd
  have htime_kc : time kc ≤ time k + 3 * system.Δ :=
    le_trans (h_mono kc k' hkc_hi) hk'time
  exact ⟨kc, hkc_lo, htime_kc, bvc, hbvc, hrnd_eq⟩

/-! ## §5 Theorem 1 (network-trace) — Block Availability -/

/-- The trace `λ k => (networkTrace system time k).base : Trace BelugaState`,
which is what the §5 properties (`BlockAvailability`, etc.) range over. -/
def networkBelugaTrace (system : BlockSynchroniserSystem) (time : Nat → Nat) :
    Trace BelugaState :=
  fun k => (networkTrace system time k).base

/-- Helper: emittedOperations grow monotonically along `networkTrace`. -/
private lemma networkBelugaTrace_emittedOperations_monotone
    (system : BlockSynchroniserSystem) (time : Nat → Nat) (k₁ k₂ : Nat) (h_le : k₁ ≤ k₂) :
    ∀ op ∈ (networkTrace system time k₁).base.emittedOperations,
      op ∈ (networkTrace system time k₂).base.emittedOperations := by
  induction h_le with
  | refl => intro _ h; exact h
  | step _ ih =>
    intro op hop
    rename_i k_mid _
    have ih' := ih op hop
    show op ∈ (networkStep system (networkTrace system time k_mid)
                (time (k_mid + 1))).base.emittedOperations
    exact networkStep_emittedOperations_monotone system _ _ op ih'

/-- **Theorem 1 (paper §5).** Network-trace formulation: every accepted
block is eventually stored. -/
theorem network_theorem1_block_availability
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_time_unbounded : ∀ T, ∃ k, time k ≥ T)
    (h_prim : PartiallySynchronousFairness system time) :
    Properties.BlockAvailability system (networkBelugaTrace system time) := by
  intro k vid d h_honest h_acc
  -- Step 1: Find a post-GST step.
  obtain ⟨k_post, hk_post_le, hk_post_gst⟩ : ∃ k', k ≤ k' ∧ time k' ≥ system.GST := by
    obtain ⟨k', hk'⟩ := h_time_unbounded system.GST
    exact ⟨max k k', le_max_left _ _, le_trans hk' (h_mono _ _ (le_max_right _ _))⟩
  -- Step 2: Persistence of vid at k_post.
  obtain ⟨bv_post, h_bv_post⟩ :=
    network_honest_validator_persistent_trace system time vid h_honest k_post
  set r := bv_post.currentRound with hr_def
  -- Step 3: Apply schedulerFairness_holds to bring all honest to round ≥ r + 1.
  have h_persistent : ∀ vid k, isHonestValidator system vid = true →
      ∃ bv, (networkTrace system time k).base.getValidator vid = some bv :=
    fun vid k h => network_honest_validator_persistent_trace system time vid h k
  obtain ⟨k_target, hk_target_le, _, h_target_all⟩ :=
    schedulerFairness_holds system time h_mono
      h_prim.networkDelivery h_prim.actionScheduling h_prim.boundedRoundSpread h_persistent
      k_post r hk_post_gst ⟨vid, bv_post, h_honest, h_bv_post, hr_def.symm⟩
  obtain ⟨bv_target, h_bv_target, hbv_target_rnd⟩ := h_target_all vid h_honest
  -- Step 4: Find the step where vid's round transitioned r → r + 1.
  obtain ⟨k_a, bv_a, bv_a', hk_a_le, _, h_a, h_a', h_a_eq, h_a'_eq⟩ :=
    network_find_advance_step system time vid r hk_target_le bv_post bv_target
      h_bv_post h_bv_target hr_def.symm hbv_target_rnd
  have h_nodup_a := networkTrace_validators_nodup system time k_a
  have h_advance : bv_a'.currentRound = bv_a.currentRound + 1 := by rw [h_a_eq, h_a'_eq]
  -- Step 5: Apply networkStep_advance_implies_stored to get the store-disabled gate.
  have h_a'_step :
      (networkStep system (networkTrace system time k_a) (time (k_a + 1))).base.getValidator vid
        = some bv_a' := h_a'
  have h_stored_gate :=
    networkStep_advance_implies_stored system (networkTrace system time k_a) (time (k_a + 1))
      vid bv_a bv_a' h_nodup_a h_a h_a'_step h_advance
  -- Step 6: d is accepted at k_a (by emittedOperations monotonicity).
  have h_acc_at_a : HasAccepted (networkTrace system time k_a).base vid d := by
    have h_le : k ≤ k_a := le_trans hk_post_le hk_a_le
    exact networkBelugaTrace_emittedOperations_monotone system time k k_a h_le _ h_acc
  have h_acc_bool :
      hasAcceptedDigest (networkTrace system time k_a).base vid d = true := by
    unfold hasAcceptedDigest
    rw [List.any_eq_true]
    exact ⟨_, h_acc_at_a, by simp +decide⟩
  -- Step 7: Use acceptedBlockExists to get the block B with B.d = d.
  obtain ⟨B, hB_mem, hB_d⟩ :=
    network_acceptedBlockExists_trace system time vid k_a d h_acc_at_a
  have h_acc_B :
      hasAcceptedDigest (networkTrace system time k_a).base vid B.d = true := by
    rw [hB_d]; exact h_acc_bool
  have h_sto_B :
      hasStoredDigest (networkTrace system time k_a).base vid B.d = true :=
    h_stored_gate B hB_mem h_acc_B
  -- Step 8: Extract the block_store op from h_sto_B.
  unfold hasStoredDigest at h_sto_B
  rw [List.any_eq_true] at h_sto_B
  obtain ⟨op, hop_mem, hop_match⟩ := h_sto_B
  refine ⟨k_a, le_trans hk_post_le hk_a_le, ?_⟩
  cases op with
  | block_store v B' =>
    simp at hop_match
    obtain ⟨h_v, h_d⟩ := hop_match
    refine ⟨B', ?_, ?_⟩
    · show ValidatorOperation.block_store vid B' ∈
        (networkBelugaTrace system time k_a).emittedOperations
      rw [h_v] at hop_mem; exact hop_mem
    · rw [h_d]; exact hB_d
  | _ => simp at hop_match

/-! ## §5 Theorem 3 (network-trace) — Round Progression -/

/-- Helper: hasProposedFor iff there's a block_propose op in emittedOperations. -/
private lemma network_hasProposedFor_iff_mem (s : BelugaState)
    (vid : ValidatorId) (r : Round) :
    hasProposedFor s vid r = true ↔
    ∃ B, ValidatorOperation.block_propose vid B r ∈ s.emittedOperations := by
  unfold hasProposedFor
  rw [List.any_eq_true]
  constructor
  · rintro ⟨op, hop_mem, hop_match⟩
    cases op with
    | block_propose v B r' =>
      simp at hop_match
      obtain ⟨h_v, h_r⟩ := hop_match
      exact ⟨B, h_v ▸ h_r ▸ hop_mem⟩
    | _ => simp at hop_match
  · rintro ⟨B, h_mem⟩
    refine ⟨ValidatorOperation.block_propose vid B r, h_mem, ?_⟩
    simp +decide

/-- Helper: under nodup, find? on a system-registered honest validator returns
the honest pair. -/
private lemma network_isHonestValidator_of_mem
    (system : BlockSynchroniserSystem) (vid : ValidatorId)
    (h_mem : (vid, true) ∈ system.validators) :
    isHonestValidator system vid = true := by
  unfold isHonestValidator BlockSynchroniserSystem.isHonest
  have h_find : system.validators.find? (fun p => p.1 == vid) = some (vid, true) :=
    find?_of_mem_nodup _ vid true h_mem system.validatorsNodup
  have h_pred_eq :
      (fun (x : ValidatorId × Bool) => match x with | (vid_1, _) => decide (vid_1 = vid))
        = (fun p => p.1 == vid) := by
    funext p
    cases p
    show decide _ = (_ == _)
    rfl
  rw [h_pred_eq, h_find]

/-- **Theorem 3 (paper §5).** Network-trace formulation: every round
eventually has 2f+1 distinct proposers (counted across honest validators
who have advanced past that round). -/
theorem network_theorem3_round_progression
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_time_unbounded : ∀ T, ∃ k, time k ≥ T)
    (h_prim : PartiallySynchronousFairness system time) :
    Properties.RoundProgression system (networkBelugaTrace system time) := by
  intro round
  -- Honest pair list non-empty (system has honestBound ≥ 2f+1 ≥ 1).
  have hHonest := system.honestBound
  set honest_pairs := system.validators.filter (fun p => p.2 = true) with h_hp_def
  have h_hp_ne : honest_pairs ≠ [] := by
    intro h_e
    have : honest_pairs.length = 0 := by rw [h_e]; rfl
    omega
  set pair_w := honest_pairs.head h_hp_ne
  have h_pair_w_mem : pair_w ∈ honest_pairs := List.head_mem _
  have h_pw_filter := List.mem_filter.mp h_pair_w_mem
  have h_pw_in : pair_w ∈ system.validators := h_pw_filter.1
  have h_pw_true : pair_w.2 = true := by simpa using h_pw_filter.2
  set vid_w := pair_w.1 with hv_w_def
  have h_w_pair_eq : (vid_w, true) ∈ system.validators := by
    have h_eq : pair_w = (vid_w, true) := by
      apply Prod.ext
      · rfl
      · exact h_pw_true
    rw [← h_eq]; exact h_pw_in
  have h_w_honest : isHonestValidator system vid_w = true :=
    network_isHonestValidator_of_mem system vid_w h_w_pair_eq
  -- Get a post-GST step.
  obtain ⟨k₀, h_k₀_gst⟩ := h_time_unbounded system.GST
  -- Apply iterated fairness to get all honest at round ≥ round + 1.
  obtain ⟨k, _, _, h_all⟩ :=
    network_all_honest_eventually_at_round system time h_mono
      h_prim.networkDelivery h_prim.actionScheduling h_prim.boundedRoundSpread
      vid_w h_w_honest k₀ h_k₀_gst (round + 1)
  refine ⟨k, ?_⟩
  set honest_vids := honest_pairs.map Prod.fst with h_hv_def
  have h_hv_len : honest_vids.length ≥ 2 * system.f + 1 := by
    rw [h_hv_def, List.length_map]; exact hHonest
  have h_sys_nodup := system.validatorsNodup
  have h_hp_nodup_records : honest_pairs.Nodup := by
    rw [h_hp_def]
    apply List.Nodup.filter
    exact List.Nodup.of_map _ h_sys_nodup
  have h_hv_nodup : honest_vids.Nodup := by
    rw [h_hv_def]
    apply List.Nodup.map_on _ h_hp_nodup_records
    intro x hx y hy h_eq
    have hx_in : x ∈ system.validators := (List.mem_filter.mp hx).1
    have hy_in : y ∈ system.validators := (List.mem_filter.mp hy).1
    have hx_find : system.validators.find? (fun z => z.1 == x.1) = some x :=
      find?_of_mem_nodup _ x.1 x.2 hx_in h_sys_nodup
    have hy_find : system.validators.find? (fun z => z.1 == y.1) = some y :=
      find?_of_mem_nodup _ y.1 y.2 hy_in h_sys_nodup
    rw [h_eq] at hx_find
    rw [hx_find] at hy_find
    grind
  set proposers_raw := (opsAt (networkBelugaTrace system time) k).filterMap (fun op =>
    match op with
    | .block_propose vid _ r => if r = round then some vid else none
    | _ => none) with h_pr_def
  have h_subset : ∀ vid ∈ honest_vids, vid ∈ proposers_raw := by
    intro vid h_vid_mem
    obtain ⟨pair, h_pair_mem, h_pair_fst⟩ := List.mem_map.mp h_vid_mem
    have h_pair_filter := List.mem_filter.mp h_pair_mem
    have h_pair_in : pair ∈ system.validators := h_pair_filter.1
    have h_pair_true : pair.2 = true := by simpa using h_pair_filter.2
    have h_vid_pair_in : (vid, true) ∈ system.validators := by
      have h_pair_eq : pair = (vid, true) := by
        apply Prod.ext
        · exact h_pair_fst
        · exact h_pair_true
      rw [← h_pair_eq]; exact h_pair_in
    have h_vid_honest : isHonestValidator system vid = true :=
      network_isHonestValidator_of_mem system vid h_vid_pair_in
    obtain ⟨bv, h_bv, h_bv_round⟩ := h_all vid h_vid_honest
    have h_round_lt : round < bv.currentRound := by
      have : round + 1 ≤ bv.currentRound := h_bv_round
      exact this
    have h_prop := network_proposed_for_lt_currentRound system time k vid bv h_bv round h_round_lt
    obtain ⟨B, h_op⟩ := (network_hasProposedFor_iff_mem _ vid round).mp h_prop
    rw [h_pr_def]
    apply List.mem_filterMap.mpr
    refine ⟨ValidatorOperation.block_propose vid B round, h_op, ?_⟩
    simp +decide
  show proposers_raw.eraseDups.length ≥ 2 * system.f + 1
  have h_fin_subset : honest_vids.toFinset ⊆ proposers_raw.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact h_subset x hx
  have h_card_le : honest_vids.toFinset.card ≤ proposers_raw.toFinset.card :=
    Finset.card_le_card h_fin_subset
  have h_hv_card : honest_vids.toFinset.card = honest_vids.length :=
    List.toFinset_card_of_nodup h_hv_nodup
  have h_eraseDups_ge_toFinset : ∀ (l : List ValidatorId),
      l.eraseDups.length ≥ l.toFinset.card := by
    intro l
    induction' l using List.reverseRecOn with l a ih
    · rfl
    · simp +decide [ List.eraseDups_append ]
      by_cases h : a ∈ l.toFinset <;> simp_all +decide [ List.removeAll ]
      exact Nat.lt_succ_of_le ‹_›
  have h_pr_ge : proposers_raw.eraseDups.length ≥ proposers_raw.toFinset.card :=
    h_eraseDups_ge_toFinset proposers_raw
  omega

/-! ## §5 Theorem 2 (network-trace) — Causal Availability

Under `networkTrace`'s ImPoA-aware accept rule, a validator can
accept a block via the f+1 references path *without* directly
accepting its parents. The strong belugaTrace invariant
`AcceptInv.acceptedParents` therefore fails. Paper §5's prose proof
of T2 invokes a separate liveness argument — under §4.3 ImPoA's
pull mechanism, the validator eventually pulls and accepts every
causally-related block.

We state T2 with an explicit hypothesis `EventualCausalAcceptance`
capturing this paper-implicit liveness step. This is the
load-bearing axiom for T2 under ImPoA — analogous to F-1c in
`mechanization-findings.md`. -/

/-- The eventual-causal-acceptance assumption: for any honest validator
that has accepted some digest `d` corresponding to a block `B`,
every causal ancestor `B'` of `B` is eventually accepted by `vid`. -/
def EventualCausalAcceptance (system : BlockSynchroniserSystem)
    (trace : Trace BelugaState) : Prop :=
  ∀ k vid d B, isHonestValidator system vid = true →
    HasAccepted (trace k) vid d →
    getBlockByDigest (trace k) d = some B →
    ∀ B', Reaches (trace k) B B' →
      ∃ k', k ≤ k' ∧ HasAccepted (trace k') vid B'.d

/-- **Theorem 2 (paper §5).** Network-trace formulation: under the
`EventualCausalAcceptance` axiom (paper §4.3 ImPoA + pull). -/
theorem network_theorem2_causal_availability
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_eventual : EventualCausalAcceptance system (networkBelugaTrace system time)) :
    Properties.CausalAvailability system (networkBelugaTrace system time) := by
  intro k vid d B h_honest h_acc h_get B' h_reach
  exact h_eventual k vid d B h_honest h_acc h_get B' h_reach

/-! ## §5 Theorem 4 (network-trace) — Round Termination

T4 says every honest validator eventually accepts blocks from 2f+1
distinct authors at every round. Under `belugaTrace`'s `step`,
this follows from the accept-before-advance gate: at the advance
step, accept is disabled (every accepted block already stored, no
more accept candidates), so vid has accepted every round-≤-`r`
block in the pool (specifically, 2f+1 round-`r` blocks from the
`allProposedFor` gate).

Under `networkTrace` with the timeout (paper §4.2 `T_rd = 4Δ`),
vid may advance via timeout *without* accepting all round-`r`
blocks. The 2f+1 acceptances would then come later, via §4.3 ImPoA
+ pull mechanism. Like T2, this requires an explicit eventual-
acceptance hypothesis. -/

/-- The eventual-round-acceptance assumption: every honest validator
eventually accepts 2f+1 distinct authors' round-`r` blocks. Under
the network model, this is a paper §4.3 + pull liveness claim;
it is not derivable from the structural networkTrace properties
alone (cf. F-1c). -/
def EventualRoundAcceptance (system : BlockSynchroniserSystem)
    (trace : Trace BelugaState) : Prop :=
  ∀ round vid, isHonestValidator system vid →
    ∃ k,
      let ops := opsAt trace k
      let acceptedAuthors : List ValidatorId :=
        ops.filterMap (fun op =>
          match op with
          | .block_accept vid' d =>
            if vid' = vid then authorOfDigest ops round d else none
          | _ => none)
        |>.eraseDups
      acceptedAuthors.length ≥ 2 * system.f + 1

/-- **Theorem 4 (paper §5).** Network-trace formulation: under the
`EventualRoundAcceptance` axiom (paper §4.3 ImPoA + pull). -/
theorem network_theorem4_round_termination
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_eventual : EventualRoundAcceptance system (networkBelugaTrace system time)) :
    Properties.RoundTermination system (networkBelugaTrace system time) := by
  intro round vid h_honest
  exact h_eventual round vid h_honest

/-! ## §5 corollary — Beluga is a block synchronizer (network-trace) -/

/-- **Corollary (paper §5).** Network-trace formulation: Beluga
satisfies all four block-synchronizer properties. -/
theorem networkTrace_isBlockSynchronizer
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_time_unbounded : ∀ T, ∃ k, time k ≥ T)
    (h_prim : PartiallySynchronousFairness system time)
    (h_eventual_causal : EventualCausalAcceptance system (networkBelugaTrace system time))
    (h_eventual_round : EventualRoundAcceptance system (networkBelugaTrace system time)) :
    Properties.BlockSynchronizer system (networkBelugaTrace system time) :=
  ⟨network_theorem3_round_progression system time h_mono h_time_unbounded h_prim,
   network_theorem4_round_termination system time h_eventual_round,
   network_theorem1_block_availability system time h_mono h_time_unbounded h_prim,
   network_theorem2_causal_availability system time h_eventual_causal⟩

end Network
end Beluga
end BlockSynchroniser
