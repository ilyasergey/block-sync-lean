/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Beluga performance bounds — *deterministic* worst-case latency lemmas
from paper Appendix C.2.

Status: L3, L4, L5 proved (Aristotle round 3e, project 91c97602).
Probabilistic Lemmas 6, 7 and Theorem 5 (expected-latency bounds)
remain out of scope until/unless we adopt a probability framework.

Prerequisites (Phase 4.5): `BlockSynchroniser/Timing.lean` (TimeMap +
PartiallySynchronous) + `BlockSynchroniser/Beluga/Protocol.lean` (refined
`ByzantineStep` constraining the adversary to attributable Byzantine
operations).
-/
import Mathlib.Tactic
import BlockSynchroniser.System
import BlockSynchroniser.Timing
import BlockSynchroniser.Beluga.Protocol
import BlockSynchroniser.Beluga.Reputation
import BlockSynchroniser.Beluga.StepPreservation

namespace BlockSynchroniser
namespace Beluga
namespace Performance

/-! ## Latency Triangle — paper Assumption 1

The paper's Assumption 1 ("latency triangle") states that honest-to-honest
direct block delivery is faster than any relay through an intermediate
validator. At the trace-model level, this implies that after GST,
whenever all honest validators are synchronized at round `r`, they all
advance to round `r + 1` within `Δ` time. We capture this consequence
as a hypothesis for Lemmas 4 and 5.
-/

/-- Latency triangle (paper Assumption 1, adapted to the trace model):
After GST, if all honest validators are synchronized at round `r`,
then within `Δ` time they all enter round `r + 1`.

This captures the combined effect of direct honest-to-honest delivery
(Assumption 1) and bounded post-GST network delay (`Δ`) on round
advancement. -/
def LatencyTriangle
    (system : BlockSynchroniserSystem) (time : TimeMap) : Prop :=
  ∀ r k,
    time k ≥ system.GST →
    (∀ vid, isHonestValidator system vid = true →
      ∃ bv, (belugaTrace system k).getValidator vid = some bv ∧
            bv.currentRound = r) →
    ∃ k', k ≤ k' ∧
      time k' ≤ time k + system.Δ ∧
      (∀ vid, isHonestValidator system vid = true →
        ∃ bv, (belugaTrace system k').getValidator vid = some bv ∧
              bv.currentRound = r + 1)

/-
**Lemma 3 (paper Appendix C.2).**
*After GST, each honest validator will not get blamed and have its
reputation decreased by honest validators.*
-/
theorem lemma3_honest_not_blamed
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (_h_time : time.WellFormed)
    (_h_sync : PartiallySynchronous system (belugaTrace system) time)
    (_R_L : Nat) :
    ∀ vid₁ vid₂,
      isHonestValidator system vid₁ = true →
      isHonestValidator system vid₂ = true →
      ∀ k, time k ≥ system.GST →
        -- vid₂'s reputation table for vid₁ is *not* decreased between step k
        -- and any later step (relative to its value at step k).
        ∀ k' ≥ k,
          (∃ bv, (belugaTrace system k).getValidator vid₂ = some bv ∧
            ∃ bv', (belugaTrace system k').getValidator vid₂ = some bv' ∧
              bv'.reputation.lookup vid₁ ≥ bv.reputation.lookup vid₁) := by
  -- proof: aristotle (project 91c97602)
  intro vid₁ vid₂ h₁ h₂ k hk k' hk';
  have := belugaTrace_getValidator_honest system vid₂ h₂ k;
  exact ⟨ _, this.choose_spec, by obtain ⟨ bv', hbv', hrep ⟩ := belugaTrace_getValidator_reputation system vid₂ k _ this.choose_spec k' hk'; exact ⟨ bv', hbv', by simp +decide [ hrep ] ⟩ ⟩

/-
Helper: from LatencyTriangle, d+1 applications advance d+1 rounds within (d+1)*Δ.
-/
private lemma round_advance_chain
    (system : BlockSynchroniserSystem) (time : TimeMap)
    (h_time : time.WellFormed)
    (h_lt : LatencyTriangle system time) :
    ∀ d r k,
      time k ≥ system.GST →
      (∀ vid, isHonestValidator system vid = true →
        ∃ bv, (belugaTrace system k).getValidator vid = some bv ∧
              bv.currentRound = r) →
      ∃ k', k ≤ k' ∧
        time k' ≤ time k + (d + 1) * system.Δ ∧
        (∀ vid, isHonestValidator system vid = true →
          ∃ bv, (belugaTrace system k').getValidator vid = some bv ∧
                bv.currentRound = r + d + 1) := by
  -- proof: aristotle (project 91c97602)
  intro d r k hk h_round
  induction' d with d ih generalizing r k;
  · exact h_lt r k hk h_round |> fun ⟨ k', hk₁, hk₂, hk₃ ⟩ => ⟨ k', hk₁, by simpa using hk₂, hk₃ ⟩;
  · obtain ⟨ k', hk₁, hk₂, hk₃ ⟩ := ih r k hk h_round;
    obtain ⟨ k'', hk₄, hk₅, hk₆ ⟩ := h_lt ( r + d + 1 ) k' ( by linarith [ h_time.1 k k' hk₁ ] ) hk₃;
    grind

theorem lemma4_round_latency_delta
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (_h_sync : PartiallySynchronous system (belugaTrace system) time)
    (_R_L : Nat)
    (h_lt : LatencyTriangle system time) :
    ∀ r k_r,
      time k_r ≥ system.GST →
      -- Hypothesis: all honest validators are in round r at step k_r.
      (∀ vid, isHonestValidator system vid = true →
        ∃ bv, (belugaTrace system k_r).getValidator vid = some bv ∧
              bv.currentRound = r) →
      -- Hypothesis: every honest validator's reputation exceeds every
      -- malicious validator's reputation in their local view at step k_r.
      (∀ vid_h vid_m,
        isHonestValidator system vid_h = true →
        isByzantineValidator system vid_m = true →
        ∀ vid_obs, isHonestValidator system vid_obs = true →
          (∃ bv, (belugaTrace system k_r).getValidator vid_obs = some bv ∧
            bv.reputation.lookup vid_h > bv.reputation.lookup vid_m)) →
      -- Conclusion: future rounds advance with latency Δ.
      ∀ r' ≥ r,
        ∃ k', time k' ≤ time k_r + (r' - r + 1) * system.Δ ∧
          ∀ vid, isHonestValidator system vid = true →
            ∃ bv, (belugaTrace system k').getValidator vid = some bv ∧
                  bv.currentRound = r' + 1 := by
  -- proof: aristotle (project 91c97602)
  intros r k_r hk_r hr hr' r' hr'';
  have := round_advance_chain system time h_time h_lt ( r' - r ) r k_r hk_r hr;
  grind

/-
**Lemma 5 (paper Appendix C.2 — deterministic part).**
*After GST, if all honest validators enter round `r` at time `t_r`,
then for any future round `r' > r`: either the latency of round `r'`
is within `2Δ`, or at least one malicious validator is blamed by
honest validators (in which case the latency of round `r'` is at most
`3Δ`).*

This is the deterministic disjunction; the expected-latency framing
(Lemma 5 in the paper) is treated separately as Lemma 5 in the paper
text combines both. The probabilistic version is out of scope.
-/
theorem lemma5_round_latency_or_blamed
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (_h_sync : PartiallySynchronous system (belugaTrace system) time)
    (_R_L : Nat)
    (h_lt : LatencyTriangle system time) :
    ∀ r k_r,
      time k_r ≥ system.GST →
      (∀ vid, isHonestValidator system vid = true →
        ∃ bv, (belugaTrace system k_r).getValidator vid = some bv ∧
              bv.currentRound = r) →
      ∀ r' > r,
        -- Either round-r' latency is ≤ 2Δ ...
        (∃ k', time k' ≤ time k_r + (r' - r) * system.Δ + 2 * system.Δ ∧
          ∀ vid, isHonestValidator system vid = true →
            ∃ bv, (belugaTrace system k').getValidator vid = some bv ∧
                  bv.currentRound = r' + 1)
        ∨
        -- ... or some malicious validator's reputation is decreased by R_L
        -- (the "blame" event), and round-r' latency is ≤ 3Δ.
        (∃ vid_m, isByzantineValidator system vid_m = true ∧
          ∃ vid_h k', isHonestValidator system vid_h = true ∧
            (∃ bv₀ bv', (belugaTrace system k_r).getValidator vid_h = some bv₀ ∧
                        (belugaTrace system k').getValidator vid_h = some bv' ∧
                        bv'.reputation.lookup vid_m + R_L ≤
                        bv₀.reputation.lookup vid_m) ∧
            time k' ≤ time k_r + (r' - r) * system.Δ + 3 * system.Δ) := by
  -- proof: aristotle (project 91c97602)
  contrapose! h_lt;
  intro h;
  obtain ⟨ r, k_r, h₁, h₂, r', hr', h₃, h₄ ⟩ := h_lt;
  -- Apply the LatencyTriangle hypothesis to obtain the existence of such a $k'$.
  obtain ⟨ k', hk₁, hk₂, hk₃ ⟩ := h r k_r h₁ h₂;
  -- Apply the LatencyTriangle hypothesis repeatedly to obtain the existence of such a $k'$.
  have h_ind : ∀ m : ℕ, ∃ k'', k' ≤ k'' ∧ time k'' ≤ time k' + m * system.Δ ∧ (∀ vid, isHonestValidator system vid = true → ∃ bv, (belugaTrace system k'').getValidator vid = some bv ∧ bv.currentRound = r + 1 + m) := by
    intro m;
    induction' m with m ih;
    · exact ⟨ k', le_rfl, by norm_num, hk₃ ⟩;
    · obtain ⟨ k'', hk₁, hk₂, hk₃ ⟩ := ih;
      obtain ⟨ k''', hk₁', hk₂', hk₃' ⟩ := h ( r + 1 + m ) k'' ( by
        exact le_trans h₁ ( h_time.1 _ _ ( by linarith ) ) ) hk₃;
      exact ⟨ k''', by linarith, by linarith, hk₃' ⟩;
  obtain ⟨ k'', hk₁'', hk₂'', hk₃'' ⟩ := h_ind ( r' - r );
  grind

end Performance
end Beluga
end BlockSynchroniser