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

end Network
end Beluga
end BlockSynchroniser
