/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Mysticeti-Beluga liveness bundle (paper Appendix D.2).

Status: round 3d (Aristotle, project `84e08b81`) gave structured proofs
of all five main theorems delegating to 11 named infrastructure lemmas
that capture the paper's intermediate steps. The five main theorems
are fully proved; the 11 helper lemmas are stubs (still depend on the
timing model + `step` semantics + Beluga protocol facts).
-/
import Mathlib.Tactic
import BlockSynchroniser.Block
import BlockSynchroniser.System
import BlockSynchroniser.State
import BlockSynchroniser.Timing
import BlockSynchroniser.Trace
import BlockSynchroniser.Beluga.Patterns
import BlockSynchroniser.Beluga.Protocol
import BlockSynchroniser.Mysticeti.Consensus
import BlockSynchroniser.Mysticeti.Safety

namespace BlockSynchroniser
namespace Mysticeti
namespace Liveness

open Beluga

/-! ## Infrastructure lemmas for liveness proofs

These lemmas capture key intermediate steps from the paper proofs in
Appendix D.2. Each depends on the timing model and the `belugaTrace`
execution. They are stated as standalone lemmas so the main theorems
compose them cleanly, matching the paper's proof structure.
-/

/-- After GST, honest validators enter the same round within `3Δ` (paper
Lemma 1 applied to Beluga). -/
lemma honest_round_entry_within_3delta
    (system : BlockSynchroniserSystem)
    (time : TimeMap) (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (r : Round) (vid : ValidatorId)
    (h_honest : isHonestValidator system vid = true)
    (k : ℕ) (h_gst : time k ≥ system.GST) :
    ∀ vid', isHonestValidator system vid' = true →
      ∃ k', time k' ≤ time k + 3 * system.Δ ∧
        (∃ bv ∈ (belugaTrace system k').validators,
          bv.1 = vid' ∧ bv.2.currentRound ≥ r) := by
  sorry

/-- After GST, the honest leader's round-`r` block is created and
disseminated within `Δ` (paper §4.2). -/
lemma leader_block_disseminated_within_delta
    (system : BlockSynchroniserSystem)
    (time : TimeMap) (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (r : Round) (vid_leader : ValidatorId)
    (h_honest : isHonestValidator system vid_leader = true)
    (h_leader : vid_leader = leaderOf system r)
    (k : ℕ) (h_gst : time k ≥ system.GST) :
    ∃ k', time k' ≤ time k + system.Δ ∧
      ∃ B_L ∈ (belugaTrace system k').blocks,
        B_L.author = vid_leader ∧ B_L.r = r := by
  sorry

/-- After GST, an honest validator references the leader block within `4Δ`
(combines round-entry + leader dissemination + parent selection). -/
lemma honest_references_leader_within_4delta
    (system : BlockSynchroniserSystem)
    (time : TimeMap) (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (r : Round) (vid_leader vid_referencer : ValidatorId)
    (h_leader_honest : isHonestValidator system vid_leader = true)
    (h_ref_honest : isHonestValidator system vid_referencer = true)
    (h_leader : vid_leader = leaderOf system r)
    (k : ℕ) (h_gst : time k ≥ system.GST) :
    ∃ k', time k' ≤ time k + 4 * system.Δ ∧
      (∃ B ∈ (belugaTrace system k').blocks,
        B.author = vid_referencer ∧ B.r = r + 1 ∧
        ∃ B_L ∈ (belugaTrace system k').blocks,
          B_L.author = vid_leader ∧ B_L.r = r ∧
          B_L.d ∈ B.parents) := by
  sorry

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
          (∃ B ∈ (belugaTrace system k').blocks,
            B.author = vid_referencer ∧ B.r = r + 1 ∧
            ∃ B_L ∈ (belugaTrace system k').blocks,
              B_L.author = vid_leader ∧ B_L.r = r ∧
              B_L.d ∈ B.parents) := by
  intro r vid_leader vid_referencer h_leader_honest h_ref_honest h_leader k h_gst
  exact honest_references_leader_within_4delta system time h_time h_sync
    r vid_leader vid_referencer h_leader_honest h_ref_honest h_leader k h_gst

/-- After GST, `2f+1` honest validators reference the leader block,
forming a certificate within `4Δ` (paper Lemma 8 + certificate pattern). -/
lemma honest_validators_certify_leader
    (system : BlockSynchroniserSystem)
    (time : TimeMap) (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (r : Round) (vid_leader : ValidatorId)
    (h_honest : isHonestValidator system vid_leader = true)
    (h_leader : vid_leader = leaderOf system r)
    (k : ℕ) (h_gst : time k ≥ system.GST) :
    ∃ k', time k' ≤ time k + 4 * system.Δ ∧
      (∃ B_L ∈ (belugaTrace system k').blocks,
        isLeaderBlock system B_L ∧ B_L.r = r ∧
        certified system (belugaTrace system k') B_L) := by
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
          (∃ B_L ∈ (belugaTrace system k').blocks,
            isLeaderBlock system B_L ∧ B_L.r = r ∧
            certified system (belugaTrace system k') B_L) := by
  intro r vid_leader h_honest h_leader k h_gst
  exact honest_validators_certify_leader system time h_time h_sync
    r vid_leader h_honest h_leader k h_gst

/-- Three consecutive honest leader blocks produce direct-commit decisions
(paper Appendix D.2, used in Lemma 11). Uses Lemma 10 (pigeonhole) and
Lemma 9 (certification). -/
lemma three_consecutive_honest_direct_commit
    (system : BlockSynchroniserSystem)
    (time : TimeMap) (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length
                = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i)
    (startRound : Round) (k₀ : ℕ) (h_gst : time k₀ ≥ system.GST) :
    ∃ r₁ ≥ startRound, ∃ k' ≥ k₀,
      (∀ B_L ∈ (belugaTrace system k').blocks,
        isLeaderBlock system B_L →
        (B_L.r = r₁ ∨ B_L.r = r₁ + 1 ∨ B_L.r = r₁ + 2) →
        directDecide system (belugaTrace system k') B_L = Decision.ToCommit) := by
  obtain ⟨r₁, hr₁_ge, _, h_honest₁, h_honest₂, h_honest₃⟩ :=
    Safety.lemma10_round_robin_pigeonhole system startRound hN hHonest h_ids
  sorry

/-- Backward induction: once three consecutive honest leaders are committed,
earlier undecided leader blocks get decided via the indirect decision rule. -/
lemma backward_induction_decides_earlier_rounds
    (system : BlockSynchroniserSystem)
    (r : Round) (r₁ : Round) (k' : ℕ)
    (h_r₁_gt : r₁ > r + 2)
    (h_committed : ∀ B_L ∈ (belugaTrace system k').blocks,
      isLeaderBlock system B_L →
      (B_L.r = r₁ ∨ B_L.r = r₁ + 1 ∨ B_L.r = r₁ + 2) →
      directDecide system (belugaTrace system k') B_L = Decision.ToCommit) :
    ∀ B_L ∈ (belugaTrace system k').blocks,
      isLeaderBlock system B_L → B_L.r = r →
      directDecide system (belugaTrace system k') B_L ≠ Decision.Undecided := by
  sorry

/-
After GST, any round-`r` leader block eventually has a non-Undecided
direct decision. Encapsulates the full argument from Lemma 10 (three
consecutive honest leaders), Lemma 9 (certification), and backward
induction (earlier rounds decided via indirect rule).
-/
lemma eventual_decision_core
    (system : BlockSynchroniserSystem)
    (time : TimeMap) (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (r : Round) (k₀ : ℕ) (h_gst : time k₀ ≥ system.GST) :
    ∃ k', k' ≥ k₀ ∧
      (∀ B_L ∈ (belugaTrace system k').blocks,
        isLeaderBlock system B_L → B_L.r = r →
        directDecide system (belugaTrace system k') B_L ≠ Decision.Undecided) := by
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
  intro r k₀ h_gst
  exact eventual_decision_core system time h_time h_sync r k₀ h_gst

/-- From `2f+1` references by distinct validators, at least `f+1` are honest
(quorum argument: at most `f` are Byzantine). -/
lemma at_least_f_plus_one_honest_referencers
    (system : BlockSynchroniserSystem)
    (B : Block) (k₀ : ℕ)
    (h_refs : ((((belugaTrace system k₀).blocks).filter (fun B' =>
        decide (B'.r > B.r) && B'.parents.contains B.d)
      ).map (·.author)).eraseDups.length ≥ 2 * system.f + 1) :
    ∃ honest_refs : List ValidatorId,
      honest_refs.length ≥ system.f + 1 ∧
      ∀ vid ∈ honest_refs, isHonestValidator system vid = true ∧
        ∃ B' ∈ (belugaTrace system k₀).blocks,
          B'.author = vid ∧ B'.r > B.r ∧ B'.parents.contains B.d = true := by
  sorry

/-- Honest blocks are eventually received by all honest validators (post-GST
delivery). Combined with ImPoA, `f+1` honest references form an implicit
proof-of-availability certificate. -/
lemma honest_blocks_eventually_received
    (system : BlockSynchroniserSystem)
    (time : TimeMap) (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (vid : ValidatorId) (d : BlockDigest)
    (h_honest : isHonestValidator system vid = true)
    (k₀ : ℕ) (h_gst : time k₀ ≥ system.GST)
    (h_available : ∃ honest_refs : List ValidatorId,
      honest_refs.length ≥ system.f + 1 ∧
      ∀ v ∈ honest_refs, isHonestValidator system v = true ∧
        ∃ B' ∈ (belugaTrace system k₀).blocks,
          B'.author = v ∧ B'.parents.contains d = true) :
    ∃ k' ≥ k₀, HasAccepted (belugaTrace system k') vid d := by
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
        ((((belugaTrace system k₀).blocks).filter (fun B' =>
            decide (B'.r > B.r) && B'.parents.contains B.d)
          ).map (·.author)).eraseDups.length ≥ 2 * system.f + 1 →
        ∃ k' ≥ k₀, HasAccepted (belugaTrace system k') vid B.d := by
  intro B vid h_honest k₀ h_gst h_refs
  -- Step 1: At least f+1 honest validators reference B (quorum argument).
  obtain ⟨honest_refs, h_count, h_props⟩ :=
    at_least_f_plus_one_honest_referencers system B k₀ h_refs
  -- Step 2: These f+1 honest blocks form an ImPoA certificate.
  have h_available : ∃ honest_refs' : List ValidatorId,
      honest_refs'.length ≥ system.f + 1 ∧
      ∀ v ∈ honest_refs', isHonestValidator system v = true ∧
        ∃ B' ∈ (belugaTrace system k₀).blocks,
          B'.author = v ∧ B'.parents.contains B.d = true := by
    exact ⟨honest_refs, h_count, fun v hv => by
      obtain ⟨h_hon, B', hB'_mem, hB'_auth, _, hB'_ref⟩ := h_props v hv
      exact ⟨h_hon, B', hB'_mem, hB'_auth, hB'_ref⟩⟩
  exact honest_blocks_eventually_received system time h_time h_sync
    vid B.d h_honest k₀ h_gst h_available

/-- After GST, any to-commit leader block is referenced by `2f+1` subsequent
blocks (since it was certified). Bridges Lemma 11 to Lemma 12. -/
lemma committed_leader_has_2f_plus_1_refs
    (system : BlockSynchroniserSystem)
    (k' : ℕ) (B : Block)
    (_h_in : B ∈ (belugaTrace system k').blocks)
    (_h_leader : isLeaderBlock system B)
    (h_commit : directDecide system (belugaTrace system k') B = Decision.ToCommit) :
    ((((belugaTrace system k').blocks).filter (fun B' =>
        decide (B'.r > B.r) && B'.parents.contains B.d)
      ).map (·.author)).eraseDups.length ≥ 2 * system.f + 1 := by
  have h_certificate : certificatePatternAtB system (belugaTrace system k') B (B.r + 2) := by
    unfold directDecide at h_commit; aesop
  unfold certificatePatternAtB at h_certificate
  simp_all +decide
  refine lt_of_lt_of_le h_certificate ?_
  have h_subset : List.toFinset (List.map (fun x => x.author)
      (List.filter (fun B' => B'.r == B.r + 2 && decide (B.d ∈ B'.parents))
        (SystemState.blocks (belugaTrace system k')))) ⊆
    List.toFinset (List.map (fun x => x.author)
      (List.filter (fun B' => decide (B.r < B'.r) && decide (B.d ∈ B'.parents))
        (SystemState.blocks (belugaTrace system k')))) := by
    simp +decide [Finset.subset_iff]; grind
  have h_card : ∀ (l : List ValidatorId),
      List.length (List.eraseDups l) = Finset.card (List.toFinset l) := by
    intro l
    induction l using List.reverseRecOn with
    | nil => simp
    | append_singleton l ih =>
      simp_all +decide [List.eraseDups_append]
      by_cases h : ih ∈ l.toFinset <;> simp_all +decide [List.removeAll]
      simp +decide [List.eraseDups_cons]
  rw [h_card, h_card]; exact Finset.card_le_card h_subset

/-- After GST, if one honest validator has accepted a block, every other
honest validator will eventually accept it too (Beluga availability
guarantees, paper §4.3). -/
lemma honest_validator_eventually_accepts
    (system : BlockSynchroniserSystem)
    (time : TimeMap) (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (vid_acc vid_h : ValidatorId)
    (h_acc_honest : isHonestValidator system vid_acc = true)
    (h_h_honest : isHonestValidator system vid_h = true)
    (B : Block) (k : ℕ) (h_gst : time k ≥ system.GST)
    (h_accepted : HasAccepted (belugaTrace system k) vid_acc B.d) :
    ∃ k' ≥ k, HasAccepted (belugaTrace system k') vid_h B.d := by
  sorry

/-- Once an honest validator has accepted a block, the block's payload
transactions are in that validator's ordered output (paper §4.3 +
consensus ordering). -/
lemma accepted_implies_in_order
    (system : BlockSynchroniserSystem)
    (order : TransactionOrder)
    (vid_h : ValidatorId)
    (h_honest : isHonestValidator system vid_h = true)
    (B : Block) (tx : Transaction)
    (h_tx : tx ∈ B.payload) (k' : ℕ)
    (h_accepted : HasAccepted (belugaTrace system k') vid_h B.d) :
    tx ∈ order vid_h := by
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
    ∀ vid_acc, isHonestValidator system vid_acc = true →
    ∀ k, time k ≥ system.GST →
    ∀ B, B ∈ (belugaTrace system k).blocks →
         HasAccepted (belugaTrace system k) vid_acc B.d →
    ∀ tx, tx ∈ B.payload →
    ∀ vid_h, isHonestValidator system vid_h = true →
      tx ∈ order vid_h := by
  intro vid_acc h_acc_honest k h_gst B h_B_in h_accepted tx h_tx vid_h h_vid_h_honest
  -- By Beluga availability (§4.3): since vid_acc has accepted B post-GST,
  -- all honest validators eventually accept B.
  have h_vid_h_accepts : ∃ k' ≥ k, HasAccepted (belugaTrace system k') vid_h B.d :=
    honest_validator_eventually_accepts system time h_time h_sync
      vid_acc vid_h h_acc_honest h_vid_h_honest B k h_gst h_accepted
  obtain ⟨k', _, h_acc'⟩ := h_vid_h_accepts
  -- Once vid_h has accepted B, its transactions are in vid_h's ordered output.
  exact accepted_implies_in_order system order vid_h h_vid_h_honest B tx h_tx k' h_acc'

end Liveness
end Mysticeti
end BlockSynchroniser
