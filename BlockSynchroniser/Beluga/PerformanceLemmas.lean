/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Beluga performance bounds — *deterministic* worst-case latency lemmas
from paper Appendix C.2.

Status: theorem statements + verbatim paper proof sketches; proofs are
`sorry`. Probabilistic Lemmas 6, 7 and Theorem 5 (expected-latency
bounds) remain out of scope until/unless we adopt a probability
framework.

Prerequisites (Phase 4.5): `BlockSynchroniser/Timing.lean` (TimeMap +
PartiallySynchronous) + `BlockSynchroniser/Beluga/Protocol.lean` (refined
`ByzantineStep` constraining the adversary to attributable Byzantine
operations).
-/
import BlockSynchroniser.System
import BlockSynchroniser.Timing
import BlockSynchroniser.Beluga.Protocol
import BlockSynchroniser.Beluga.Reputation

namespace BlockSynchroniser
namespace Beluga
namespace Performance

/--
**Lemma 3 (paper Appendix C.2).**
*After GST, each honest validator will not get blamed and have its
reputation decreased by honest validators.*

PROVIDED SOLUTION (paper Appendix C.2)
Recall from Section 4.2 that a validator `v_i` has its reputation
decreased by honest validators only if `f+1` validators report having
invoked the pull protocol to synchronize `v_i`'s blocks. An honest
validator `v_j` invokes the pull protocol upon receiving a block `B'_k`
from a validator `v_k`, where `v_k` references `v_i`'s round `r-1`
block `B'_k.r-1`, while `v_j` has not yet received `B'_k.r-1` directly.
By Assumption 1 (latency triangle), if `v_i` is honest and sends
`B'_i^{r-1}` to `v_j`, then `v_j` receives `B'_i^{r-1}` directly before
receiving it via an intermediate validator `v_k` that references it in
`B'_k`. Hence, `v_j` does not invoke the pull protocol for `B'_i^{r-1}`
and does not report `v_j`. Since there are at most `f` malicious
validators, an honest `v_i` cannot be reported by `f+1` validators and
therefore is not blamed by honest validators.
-/
theorem lemma3_honest_not_blamed
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (R_L : Nat) :
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
  sorry

/--
**Lemma 4 (paper Appendix C.2).**
*After GST, if all honest validators enter round `r` at time `t_r` and
have their reputation higher than that of any malicious validator, then
for any future round `r' ≥ r`, the latency of round `r'` is `Δ`.*

PROVIDED SOLUTION (paper Appendix C.2)
Since all honest validators have higher reputation than any malicious
validator, by the reputation-based push protocol, honest validators
reference round-`r-1` blocks from honest validators when creating their
round `r` blocks. After GST, these round `r` blocks are accepted by all
honest validators within `Δ` (without invoking the pull protocol).
Consequently, round `r` has latency `Δ`, and all honest validators
enter round `r+1` at time `t_r + Δ`. By induction, the latency of any
future round `r' ≥ r` is `Δ`.
-/
theorem lemma4_round_latency_delta
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (R_L : Nat) :
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
  sorry

/--
**Lemma 5 (paper Appendix C.2 — deterministic part).**
*After GST, if all honest validators enter round `r` at time `t_r`,
then for any future round `r' > r`: either the latency of round `r'`
is within `2Δ`, or at least one malicious validator is blamed by
honest validators (in which case the latency of round `r'` is at most
`3Δ`).*

This is the deterministic disjunction; the expected-latency framing
(Lemma 5 in the paper) is treated separately as Lemma 5 in the paper
text combines both. The probabilistic version is out of scope.

PROVIDED SOLUTION (paper Appendix C.2)
Recall from Section 4.2 that a validator's reputation is decreased by
`R_L` only when it is reported by `f+1` honest validators. By
Lemma 3, honest validators cannot be reported. So if some malicious
`v_m` is to delay round `r'`, it must withhold its round `r'-1` block
from at least `f+1` honest validators. Honest validators that miss
`v_m`'s block invoke the pull protocol and report `v_m`. As soon as
`f+1` reports accumulate, `v_m`'s reputation drops by `R_L` and
honest validators avoid referencing it next round. The round-`r'`
latency is bounded by `2Δ` for the pull or `3Δ` if `v_m` is blamed.
-/
theorem lemma5_round_latency_or_blamed
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (R_L : Nat) :
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
  sorry

end Performance
end Beluga
end BlockSynchroniser
