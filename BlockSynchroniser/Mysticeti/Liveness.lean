/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Mysticeti-Beluga liveness bundle (paper Appendix D.2).

Status: theorem statements + paper proof sketches; proofs are `sorry`.
All five theorems below depend on the timing model from
`BlockSynchroniser/Timing.lean` and the partial-synchrony predicate
`PartiallySynchronous`. Without those, liveness can't be precisely
stated.
-/
import BlockSynchroniser.Block
import BlockSynchroniser.System
import BlockSynchroniser.State
import BlockSynchroniser.Timing
import BlockSynchroniser.Trace
import BlockSynchroniser.Beluga.Patterns
import BlockSynchroniser.Beluga.Protocol
import BlockSynchroniser.Mysticeti.Consensus

namespace BlockSynchroniser
namespace Mysticeti
namespace Liveness

open Beluga

/--
**Lemma 8 (paper Appendix D.2).**
*In Mysticeti-Beluga, after GST, an honest validator's leader block will
be referenced in the next round by every honest validator.*

PROVIDED SOLUTION (paper Appendix D)
After GST, if an honest validator enters a round `r`, then by Lemma 1
all honest validators will be able to enter the same round `r` within
`3Δ`. Then the honest leader validator (and every other honest
validator) will directly create and disseminate the round `r` leader
block `B_L^r`, which will take another `Δ` to be received by every
honest validator. Since `T_live` is set to `4Δ`, `B_L^r` will arrive
before the first honest validator times out. As validators are asked
to include leader blocks as parents, every honest validator will vote
for the leader block.
-/
theorem lemma8_leader_referenced
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time) :
    ∀ r vid_leader vid_referencer,
      isHonestValidator system vid_leader = true →
      isHonestValidator system vid_referencer = true →
      vid_leader = leaderOf system r →
      ∀ k, time k ≥ system.GST →
        ∃ k', time k' ≤ time k + 4 * system.Δ ∧
          -- vid_referencer authors a round-(r+1) block referencing vid_leader's round-r block
          (∃ B ∈ (belugaTrace system k').blocks,
            B.author = vid_referencer ∧ B.r = r + 1 ∧
            ∃ B_L ∈ (belugaTrace system k').blocks,
              B_L.author = vid_leader ∧ B_L.r = r ∧
              B_L.d ∈ B.parents) := by
  sorry

/--
**Lemma 9 (paper Appendix D.2).**
*In Mysticeti-Beluga, after GST, all honest validators will create a
certificate for the leader block proposed by an honest validator.*

PROVIDED SOLUTION (paper Appendix D)
Assume there is an honest leader block `B_L^r` in round `r`. By Lemma 8,
all honest validators will vote for `B_L^r` after GST. This means `B_L^r`
is a certified block, and all honest validators will have their round
`r+1` blocks referencing `B_L^r` as parents. By Lemma 1, every honest
validator can receive `2f+1` round `r+1` blocks from round `r+1` within
`4Δ`. Consequently, according to the parent selection employed in
Mysticeti-Beluga (Appendix D.1.2), where validators wait for `4Δ` before
giving up on round `r+2`, every honest validator can create a round
`r+2` block that references these `2f+1` round `r+1` blocks from honest
validators. In other words, every honest validator will create a
certificate for `B_L^r`.
-/
theorem lemma9_honest_certificate
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time) :
    ∀ r vid_leader,
      isHonestValidator system vid_leader = true →
      vid_leader = leaderOf system r →
      ∀ k, time k ≥ system.GST →
        ∃ k', time k' ≤ time k + 4 * system.Δ ∧
          -- The round-r leader block is certified in this state.
          (∃ B_L ∈ (belugaTrace system k').blocks,
            isLeaderBlock system B_L ∧ B_L.r = r ∧
            certified system (belugaTrace system k') B_L) := by
  sorry

/--
**Lemma 11 (paper Appendix D.2).**
*In Mysticeti-Beluga, any undecided leader block eventually gets
decided.*

PROVIDED SOLUTION (paper Appendix D)
Consider an undecided leader block in round `r`. After GST, by Lemma 10,
there will eventually be three honest leader blocks in three consecutive
rounds `k, k+1, k+2` with `k > r`. By Lemma 9, each of these honest
leader blocks will have `2f+1` certificates and can be decided as
to-commit via the direct decision rule. We now prove that by induction,
all undecided leader blocks in rounds `< k` get decided. For the base
case, any undecided leader blocks in rounds `k - 3`, `k - 2`, and `k - 1`
get decided by the to-commit leader blocks in rounds `k`, `k + 1`, and
`k + 2`, respectively, via the indirect decision rule. For the
induction step, if an undecided leader block in round `r' < k - 3` also
gets decided since `k` is higher than `r' + 2` and there are no
undecided leader blocks between `r'` and `k` (induction hypothesis).
-/
theorem lemma11_eventual_decision
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time) :
    ∀ r,
      ∀ k₀, time k₀ ≥ system.GST →
        ∃ k', k' ≥ k₀ ∧
          (∀ B_L ∈ (belugaTrace system k').blocks,
            isLeaderBlock system B_L → B_L.r = r →
            directDecide system (belugaTrace system k') B_L ≠ Decision.Undecided) := by
  sorry

/--
**Lemma 12 (paper Appendix D.2).**
*In Mysticeti-Beluga, if a block `B` is referenced by `2f + 1`
subsequent blocks, then every honest validator will eventually output
`block_accept` for `B`.*

PROVIDED SOLUTION (paper Appendix D)
If `B` is referenced by `2f + 1` subsequent blocks, at least `f + 1`
honest validators reference `B`. These `f + 1` honest blocks will
eventually be received by all honest validators. According to the
ImPoA-based pull protocol (Section 4.3), they form an implicit
proof-of-availability certificate for `B` and `B` is output via
`block_accept` by every honest validator.
-/
theorem lemma12_referenced_accepted
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time) :
    ∀ (B : Block) (vid : ValidatorId),
      isHonestValidator system vid = true →
      ∀ k₀, time k₀ ≥ system.GST →
        -- B is referenced by ≥ 2f+1 subsequent blocks at step k₀
        ((((belugaTrace system k₀).blocks).filter (fun B' =>
            decide (B'.r > B.r) && B'.parents.contains B.d)
          ).map (·.author)).eraseDups.length ≥ 2 * system.f + 1 →
        ∃ k' ≥ k₀, HasAccepted (belugaTrace system k') vid B.d := by
  sorry

/--
**Theorem 6 (paper Appendix D.2) — Mysticeti-Beluga consensus liveness.**
*In Mysticeti-Beluga, after GST, transactions will be ordered and
finalized.*

PROVIDED SOLUTION (paper Appendix D)
By Lemma 9, there will be `2f+1` certificates for each honest leader
block after GST, and the honest leader block will be decided as
to-commit by Lemma 11. By Lemma 11, all leader blocks will eventually
get decided. Therefore, validators can order all to-commit leader blocks
and their causal history blocks. Moreover, since each to-commit leader
block created is referenced by `2f+1` subsequent blocks as parents, by
Lemma 12, every honest validator will output `block_accept` for the
leader block. According to block availability and causal availability
ensured by Beluga, the leader block and its causal history blocks will
eventually be output via `block_store`. This means that all transactions
in to-commit leader blocks and their causal history blocks can be
retrieved, ordered, and finalized.
-/
theorem theorem6_consensus_liveness
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (order : TransactionOrder) :
    -- For every transaction included in some block accepted post-GST by
    -- some honest validator, every honest validator eventually has it in
    -- their ordered output.
    ∀ vid_acc, isHonestValidator system vid_acc = true →
    ∀ k, time k ≥ system.GST →
    ∀ B, B ∈ (belugaTrace system k).blocks →
         HasAccepted (belugaTrace system k) vid_acc B.d →
    ∀ tx, tx ∈ B.payload →
    ∀ vid_h, isHonestValidator system vid_h = true →
      tx ∈ order vid_h := by
  sorry

end Liveness
end Mysticeti
end BlockSynchroniser
