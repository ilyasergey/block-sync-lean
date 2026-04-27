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
    (h_delivery : NetworkDelivery system time)
    (h_scheduling : ActionScheduling system time)
    (h_spread : BoundedRoundSpread_networkTrace system time) :
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
  exact schedulerFairness_holds system time h_mono h_delivery h_scheduling h_spread
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
    (h_delivery : NetworkDelivery system time)
    (h_scheduling : ActionScheduling system time)
    (h_spread : BoundedRoundSpread_networkTrace system time) :
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
    network_lemma1_honest_round_entry system time h_mono h_delivery h_scheduling h_spread
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
    (h_delivery : NetworkDelivery system time)
    (h_scheduling : ActionScheduling system time)
    (h_spread : BoundedRoundSpread_networkTrace system time) :
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
    schedulerFairness_holds system time h_mono h_delivery h_scheduling h_spread h_persistent
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

end Network
end Beluga
end BlockSynchroniser
