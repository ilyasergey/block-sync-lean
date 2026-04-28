/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Mysticeti-Beluga liveness (paper Appendix D.2).
-/
import Mathlib.Tactic
import BlockSynchroniser.Block
import BlockSynchroniser.System
import BlockSynchroniser.State
import BlockSynchroniser.Timing
import BlockSynchroniser.Trace
import BlockSynchroniser.Beluga.Patterns
import BlockSynchroniser.Beluga.Protocol
import BlockSynchroniser.Beluga.Network
import BlockSynchroniser.Beluga.Theorems
import BlockSynchroniser.Beluga.Order
import BlockSynchroniser.Mysticeti.Consensus
import BlockSynchroniser.Mysticeti.SafetyInvariant
import BlockSynchroniser.Mysticeti.Safety

namespace BlockSynchroniser
namespace Mysticeti
namespace Liveness

open Beluga

/-! ## §D.2 post-GST liveness bundle

The §D.2 lemmas (L7–L12, T6) consume two paper-implicit per-action
liveness primitives on top of the §5 bundle: the §4.2
`block_propose` and `block_store` per-action `Δ`-bounds (the §4.2
prose's symmetric per-action treatment of the four protocol
actions, where `acceptScheduling` is already in
`BelugaPartialSynchrony` and `timeoutAdvance` covers `advance`).
We bundle these as `MysticetiBelugaSynchrony`, extending
`BelugaWithPullFairness`. Two further paper §D.1 protocol-rule
primitives handle the Mysticeti consensus-rule structural facts
that the §D.2 derivations consume:

- `leader_inclusion` — paper §D.1.2: when an honest validator at
  round `r+1` has the round-`r` leader's block in its accepted
  set, it includes that block as a parent.
- `cert_pattern_at_r2` — paper §D.1.1: when a leader block's
  certificate (`certified` / certificate pattern) holds, the
  formal `certificatePatternAtB ... B (B.r + 2)` predicate that
  `directDecide` checks is satisfied (the cert structure carries
  through to the round-`r+2` direct-decision input). -/

/-- **`MysticetiBelugaSynchrony`** — extends
`BelugaWithPullFairness` with paper §4.2 per-action liveness for
`propose`/`store` and two paper §D.1 protocol-rule primitives. -/
structure MysticetiBelugaSynchrony
    (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop
    extends Beluga.Network.BelugaWithPullFairness system time where
  /-- Paper §4.2 per-action liveness for `block_propose`. -/
  proposeScheduling : Beluga.Network.ProposeSchedulingWithPull system time
  /-- Paper §4.2 per-action liveness for `block_store`. -/
  storeScheduling   : Beluga.Network.StoreSchedulingWithPull system time
  /-- Paper §D.1.2 admission rule (Mysticeti-Beluga's prioritisation
  of leader blocks among parents): if the round-`r` leader's block
  has been accepted by an honest validator `vid` and `vid` creates
  a round-`(r+1)` block, that block's parent set contains the
  leader's block. -/
  leader_inclusion :
    ∀ (k : ℕ) (vid : ValidatorId) (B B_L : Block),
      isHonestValidator system vid = true →
      time k ≥ system.GST →
      B ∈ (Beluga.Network.networkTraceWithPull system time k).base.blocks →
      B_L ∈ (Beluga.Network.networkTraceWithPull system time k).base.blocks →
      B.author = vid →
      isLeaderBlock system B_L →
      B_L.r + 1 = B.r →
      hasAcceptedDigest (Beluga.Network.networkTraceWithPull system time k).base vid B_L.d = true →
      B_L.d ∈ B.parents
  /-- Paper §D.1.1 cert-pattern timing: a `certified` leader block
  in the trace satisfies `certificatePatternAtB` at round `r + 2`,
  the predicate `directDecide` reads. -/
  cert_pattern_at_r2 :
    ∀ (k : ℕ) (B_L : Block),
      time k ≥ system.GST →
      B_L ∈ (Beluga.Network.networkTraceWithPull system time k).base.blocks →
      isLeaderBlock system B_L →
      certified system (Beluga.Network.networkTraceWithPull system time k).base B_L →
      certificatePatternAtB system (Beluga.Network.networkTraceWithPull system time k).base B_L (B_L.r + 2)
  /-- Paper §2.1 + §D.3 item (iv): block-digest determinism — *"the
  block digest is derived from hashing the block and can be used to
  identify the same block, where an identical digest implies the
  same block"*. Two blocks in the trace with the same digest are
  equal. -/
  block_unique_by_digest :
    ∀ (k : ℕ) (B B' : Block),
      B  ∈ (Beluga.Network.networkTraceWithPull system time k).base.blocks →
      B' ∈ (Beluga.Network.networkTraceWithPull system time k).base.blocks →
      B.d = B'.d → B = B'
  /-- Paper §2.1 + §4.2: parents referenced by a block in the pool
  correspond to blocks in the pool. (Admission control accepts only
  blocks whose parents are in the validator's state, hence in the
  global pool.) -/
  parent_blocks_in_pool :
    ∀ (k : ℕ) (B : Block) (d : BlockDigest),
      B ∈ (Beluga.Network.networkTraceWithPull system time k).base.blocks →
      B.parents.contains d = true →
      ∃ B_d ∈ (Beluga.Network.networkTraceWithPull system time k).base.blocks,
        B_d.d = d


/-! ## §D.2 derived theorems

Each §D.2 lemma below takes `MysticetiBelugaSynchrony` plus the
standard BFT side conditions (`n = 3f + 1`, `|honest| = 2f + 1`,
contiguous IDs) and concludes against `networkBelugaTraceWithPull`. -/

/-- Helper: the Byzantine-count bound — in any nodup list of
registered validator IDs, at most `f` entries are Byzantine. -/
private lemma byz_bound_of_system_constraints
    (system : BlockSynchroniserSystem)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length
                = 2 * system.f + 1) :
    ∀ authors : List ValidatorId,
      authors.Nodup →
      (∀ a ∈ authors, ∃ p ∈ system.validators, p.1 = a) →
      (authors.filter (fun vid => !isHonestValidator system vid)).length ≤ system.f := by
  intros authors h_nodup h_registered
  have h_non_honest_count : (List.filter (fun vid => !isHonestValidator system vid) authors).length ≤ (List.filter (fun p => !p.2) system.validators).length := by
    have h_non_honest_subset : (List.filter (fun vid => !isHonestValidator system vid) authors).toFinset ⊆ (List.filter (fun p => !p.2) system.validators).toFinset.image (fun p => p.1) := by
      intro a ha
      simp_all +decide [isHonestValidator]
      cases h_registered a ha.1 <;> simp_all +decide [BlockSynchroniserSystem.isHonest]
      cases h : List.find? (fun x => decide (x.1 = a)) system.validators <;> simp_all +decide
      · exact False.elim <| h a |>.2 ‹_› rfl
      · grind
    have := Finset.card_le_card h_non_honest_subset
    rw [List.toFinset_card_of_nodup] at this
    · exact this.trans (Finset.card_image_le.trans (List.toFinset_card_le _))
    · exact h_nodup.filter _
  have h_partition : (List.filter (fun p => !p.2) system.validators).length + (List.filter (fun p => p.2) system.validators).length = system.n := by
    have h : ∀ (l : List (ValidatorId × Bool)), (List.filter (fun p => !p.2) l).length + (List.filter (fun p => p.2) l).length = l.length := by
      intro l; induction l <;> simp +decide [*]
      grind
    rw [h, BlockSynchroniserSystem.validatorCountCorrect]
  grind +locals

/-! ### §D.2 Lemma 1 (paper §5 L1 reused) -/

/-- Paper §5 Lemma 1: post-GST, given an honest validator at round `r`
at step `k`, every honest validator is at round `≥ r` within `4Δ`. -/
theorem honest_round_entry
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h_sync : MysticetiBelugaSynchrony system time)
    (r : Round) (k : ℕ)
    (h_gst : time k ≥ system.GST)
    (h_witness : ∃ vid_w bv_w, isHonestValidator system vid_w = true ∧
      (Beluga.Network.networkTraceWithPull system time k).base.getValidator vid_w = some bv_w ∧
      bv_w.currentRound = r) :
    ∃ k', k ≤ k' ∧ time k' ≤ time k + 4 * system.Δ ∧
      ∀ vid, isHonestValidator system vid = true →
        ∃ bv, (Beluga.Network.networkTraceWithPull system time k').base.getValidator vid = some bv ∧
              bv.currentRound ≥ r :=
  Beluga.Network.lemma1_honest_round_entry
    h_sync.toBelugaWithPullFairness.toBelugaPartialSynchrony r k h_gst h_witness

/-! ### §D.2 Lemma 7 — leader propose (Δ within `5Δ`) -/

/-- Paper §D.2 Lemma 7 (intermediate): post-GST, given an honest validator
at round `r` at step `k`, the round-`r` honest leader's block exists
in the trace within `5Δ`.

Composes `honest_round_entry` (4Δ to bring the leader to round `r`)
with `proposeScheduling` (Δ to fire the propose action at round `r`).
The case where the leader has already passed round `r` (so already
proposed for `r`) is handled by the round-monotone protocol invariant. -/
theorem leader_propose
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h_sync : MysticetiBelugaSynchrony system time)
    (r : Round) (vid_leader : ValidatorId) (k : ℕ)
    (h_honest : isHonestValidator system vid_leader = true)
    (_h_leader : vid_leader = leaderOf system r)
    (h_gst : time k ≥ system.GST)
    (h_witness : ∃ vid_w bv_w, isHonestValidator system vid_w = true ∧
      (Beluga.Network.networkTraceWithPull system time k).base.getValidator vid_w = some bv_w ∧
      bv_w.currentRound = r) :
    ∃ k', k ≤ k' ∧ time k' ≤ time k + 5 * system.Δ ∧
      ∃ B_L ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks,
        B_L.author = vid_leader ∧ B_L.r = r := by
  -- Step 1: by L1, the leader reaches round ≥ r within 4Δ.
  obtain ⟨k₁, hk₁_lo, hk₁_time, hk₁_all⟩ :=
    honest_round_entry h_sync r k h_gst h_witness
  obtain ⟨bv_lead₁, h_lead_get₁, h_lead_round₁⟩ := hk₁_all vid_leader h_honest
  -- Step 2: case-split on whether the leader is exactly at round r or strictly past.
  rcases Nat.lt_or_ge r bv_lead₁.currentRound with h_past | h_at
  · -- Already past: the leader has proposed for r at some earlier step.
    -- By round-monotone propose-witnessing, a propose op for round r exists.
    have h_proposed :=
      Beluga.Network.network_proposed_for_lt_currentRoundWithPull
        system time k₁ vid_leader bv_lead₁ h_lead_get₁ r h_past
    obtain ⟨B, h_op⟩ :=
      Beluga.Network.hasProposedFor_implies_propose_op _ vid_leader r h_proposed
    -- The propose op witnesses a block in the pool by digest membership.
    have h_invariant := Beluga.Network.network_propose_op_invariant_traceWithPull system time k₁
    obtain ⟨h_author, h_round, _h_digest, h_in_blocks⟩ := h_invariant vid_leader B r h_op
    refine ⟨k₁, hk₁_lo, ?_, B, h_in_blocks, h_author, h_round⟩
    have : 4 * system.Δ ≤ 5 * system.Δ := by omega
    omega
  · -- Exactly at round r: apply proposeScheduling.
    -- Either the leader has already proposed (block exists), or the action fires within Δ.
    have h_eq : bv_lead₁.currentRound = r := Nat.le_antisymm h_at h_lead_round₁
    have h_post_gst₁ : time k₁ ≥ system.GST :=
      le_trans h_gst (h_sync.timeMonotone k k₁ hk₁_lo)
    by_cases h_already :
        hasProposedFor (Beluga.Network.networkTraceWithPull system time k₁).base
          vid_leader bv_lead₁.currentRound = true
    · -- Already proposed at step k₁: extract the block.
      rw [h_eq] at h_already
      obtain ⟨B, h_op⟩ :=
        Beluga.Network.hasProposedFor_implies_propose_op _ vid_leader r h_already
      have h_invariant := Beluga.Network.network_propose_op_invariant_traceWithPull system time k₁
      obtain ⟨h_author, h_round, _h_digest, h_in_blocks⟩ := h_invariant vid_leader B r h_op
      refine ⟨k₁, hk₁_lo, ?_, B, h_in_blocks, h_author, h_round⟩
      have : 4 * system.Δ ≤ 5 * system.Δ := by omega
      omega
    · -- Not yet proposed: fire the propose-action scheduling.
      have h_not : hasProposedFor (Beluga.Network.networkTraceWithPull system time k₁).base
          vid_leader bv_lead₁.currentRound = false := by
        cases h : hasProposedFor (Beluga.Network.networkTraceWithPull system time k₁).base
            vid_leader bv_lead₁.currentRound
        · rfl
        · exact absurd h h_already
      obtain ⟨k₂, hk₂_lo, hk₂_time, B, h_in_blocks, h_author, h_round⟩ :=
        h_sync.proposeScheduling k₁ vid_leader bv_lead₁ h_honest h_post_gst₁ h_lead_get₁ h_not
      refine ⟨k₂, le_trans hk₁_lo hk₂_lo, ?_, B, h_in_blocks, h_author, ?_⟩
      · -- time k₂ ≤ time k₁ + Δ ≤ time k + 4Δ + Δ = time k + 5Δ.
        omega
      · -- B.r = bv_lead₁.currentRound = r.
        rw [h_round, h_eq]

/-! ### §D.2 Lemma 7 (full form: leader referenced as parent) -/

/-- Paper §D.2 Lemma 7: post-GST, every honest validator's round-(r+1)
block has the round-`r` honest leader's block as parent. -/
theorem honest_ref_leader
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h_sync : MysticetiBelugaSynchrony system time)
    (r : Round) (vid_leader vid_referencer : ValidatorId) (k : ℕ)
    (h_lead_honest : isHonestValidator system vid_leader = true)
    (h_ref_honest : isHonestValidator system vid_referencer = true)
    (h_leader : vid_leader = leaderOf system r)
    (h_gst : time k ≥ system.GST)
    (h_witness : ∃ vid_w bv_w, isHonestValidator system vid_w = true ∧
      (Beluga.Network.networkTraceWithPull system time k).base.getValidator vid_w = some bv_w ∧
      bv_w.currentRound = r) :
    ∃ k', k ≤ k' ∧
      (∃ B ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks,
        B.author = vid_referencer ∧ B.r = r + 1 ∧
        ∃ B_L ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks,
          B_L.author = vid_leader ∧ B_L.r = r ∧
          B_L.d ∈ B.parents) := by
  -- Step 1: leader's round-r block exists at step k₁ ≤ k + 5Δ.
  obtain ⟨k₁, hk₁_lo, _hk₁_time, B_L, h_BL_in, h_BL_author, h_BL_round⟩ :=
    leader_propose h_sync r vid_leader k h_lead_honest h_leader h_gst h_witness
  have h_post_gst₁ : time k₁ ≥ system.GST :=
    le_trans h_gst (h_sync.timeMonotone k k₁ hk₁_lo)
  -- Step 2: every honest validator reaches round ≥ r + 2 eventually.
  obtain ⟨k₂, hk₂_lo, hk₂_gst, h_all_at_r2⟩ :=
    Beluga.Network.network_all_honest_eventually_at_roundWithPull
      system time h_sync.timeMonotone
      h_sync.networkDelivery h_sync.timeoutAdvance h_sync.boundedRoundSpread
      vid_referencer h_ref_honest k₁ h_post_gst₁ (r + 2)
  obtain ⟨bv_ref, h_ref_get, h_ref_round⟩ := h_all_at_r2 vid_referencer h_ref_honest
  -- Step 3: vid_ref's currentRound > r + 1, so it has proposed for r + 1.
  have h_ref_gt : r + 1 < bv_ref.currentRound :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (r + 1)) h_ref_round
  have h_proposed_r1 :
      hasProposedFor (Beluga.Network.networkTraceWithPull system time k₂).base
        vid_referencer (r + 1) = true :=
    Beluga.Network.network_proposed_for_lt_currentRoundWithPull
      system time k₂ vid_referencer bv_ref h_ref_get (r + 1) h_ref_gt
  -- Step 4: extract B_ref via the propose-op invariant.
  obtain ⟨B_ref, h_op⟩ :=
    Beluga.Network.hasProposedFor_implies_propose_op _ vid_referencer (r + 1) h_proposed_r1
  obtain ⟨h_ref_author, h_ref_r, _h_ref_digest, h_ref_in⟩ :=
    Beluga.Network.network_propose_op_invariant_traceWithPull system time k₂
      vid_referencer B_ref (r + 1) h_op
  -- Step 5: B_L persists in the pool from k₁ to k₂.
  have h_BL_in_k₂ :
      B_L ∈ (Beluga.Network.networkTraceWithPull system time k₂).base.blocks :=
    Beluga.Network.network_blocks_monotone_traceWithPull system time k₁ k₂ hk₂_lo B_L h_BL_in
  -- Step 6: vid_ref eventually accepts B_L; pick step k₃ ≥ k₂ where it has.
  obtain ⟨k₃, hk₃_lo, h_acc_bool⟩ :=
    Beluga.Network.network_in_pool_eventually_accepted_withPull
      system time h_sync.timeMonotone h_sync.inPoolDelivery h_sync.acceptScheduling
      k₂ vid_referencer B_L h_ref_honest hk₂_gst h_BL_in_k₂
  -- Step 7: lift everything to step k₃ via blocks-monotonicity.
  have h_BL_in_k₃ :
      B_L ∈ (Beluga.Network.networkTraceWithPull system time k₃).base.blocks :=
    Beluga.Network.network_blocks_monotone_traceWithPull system time k₂ k₃ hk₃_lo B_L h_BL_in_k₂
  have h_ref_in_k₃ :
      B_ref ∈ (Beluga.Network.networkTraceWithPull system time k₃).base.blocks :=
    Beluga.Network.network_blocks_monotone_traceWithPull system time k₂ k₃ hk₃_lo B_ref h_ref_in
  have h_post_gst₃ : time k₃ ≥ system.GST :=
    le_trans hk₂_gst (h_sync.timeMonotone k₂ k₃ hk₃_lo)
  -- Step 8: apply leader_inclusion to conclude B_L.d ∈ B_ref.parents.
  have h_isLeader : isLeaderBlock system B_L := by
    unfold isLeaderBlock
    rw [h_BL_author, h_leader, h_BL_round]
  have h_round_succ : B_L.r + 1 = B_ref.r := by
    rw [h_BL_round, h_ref_r]
  have h_BLd_in_parents : B_L.d ∈ B_ref.parents :=
    h_sync.leader_inclusion k₃ vid_referencer B_ref B_L
      h_ref_honest h_post_gst₃ h_ref_in_k₃ h_BL_in_k₃ h_ref_author
      h_isLeader h_round_succ h_acc_bool
  -- Conclude.
  refine ⟨k₃, le_trans hk₁_lo (le_trans hk₂_lo hk₃_lo), B_ref, h_ref_in_k₃,
    h_ref_author, h_ref_r, B_L, h_BL_in_k₃, h_BL_author, h_BL_round, h_BLd_in_parents⟩

/-! ### §D.2 Lemma 8 — leader certified -/

/-- Paper §D.2 Lemma 8: post-GST, the round-`r` honest leader's block
becomes `certified` (certificate pattern). -/
theorem honest_certify_leader
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h_sync : MysticetiBelugaSynchrony system time)
    (r : Round) (vid_leader : ValidatorId) (k : ℕ)
    (h_honest : isHonestValidator system vid_leader = true)
    (h_leader : vid_leader = leaderOf system r)
    (h_gst : time k ≥ system.GST)
    (h_witness : ∃ vid_w bv_w, isHonestValidator system vid_w = true ∧
      (Beluga.Network.networkTraceWithPull system time k).base.getValidator vid_w = some bv_w ∧
      bv_w.currentRound = r) :
    ∃ k', k ≤ k' ∧
      (∃ B_L ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks,
        isLeaderBlock system B_L ∧ B_L.r = r ∧
        certified system (Beluga.Network.networkTraceWithPull system time k').base B_L) := by
  sorry

/-! ### §D.2 Lemma 9 corollary — three consecutive direct commits -/

/-- Paper §D.2 Lemma 9 corollary: with three consecutive honest leaders,
their leader blocks all direct-commit `ToCommit`. -/
theorem three_consec_commit
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h_sync : MysticetiBelugaSynchrony system time)
    (_hN : system.n = 3 * system.f + 1)
    (_hHonest : (system.validators.filter (fun p => p.2 = true)).length = 2 * system.f + 1)
    (_h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i)
    (startRound : Round) (k₀ : ℕ) (h_gst : time k₀ ≥ system.GST) :
    ∃ r₁ ≥ startRound, ∃ k' ≥ k₀,
      (∀ B_L ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks,
        isLeaderBlock system B_L →
        (B_L.r = r₁ ∨ B_L.r = r₁ + 1 ∨ B_L.r = r₁ + 2) →
        directDecide system (Beluga.Network.networkTraceWithPull system time k').base B_L
          = Decision.ToCommit) := by
  sorry

/-! ### §D.2 Lemma 11 backward step -/

/-- Paper §D.2 Lemma 11 backward step: given three consecutive committed
leaders at rounds `r₁, r₁+1, r₁+2` (with `r₁ > r + 2`), every leader
at round `r` is decided (non-`Undecided`). -/
theorem backward_induction
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (_h_sync : MysticetiBelugaSynchrony system time)
    (_hN : system.n = 3 * system.f + 1)
    (_hHonest : (system.validators.filter (fun p => p.2 = true)).length = 2 * system.f + 1)
    (_h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i)
    (r r₁ : Round) (k' : ℕ) (h_r₁_gt : r₁ > r + 2)
    (h_committed : ∀ B_L ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks,
      isLeaderBlock system B_L →
      (B_L.r = r₁ ∨ B_L.r = r₁ + 1 ∨ B_L.r = r₁ + 2) →
      directDecide system (Beluga.Network.networkTraceWithPull system time k').base B_L
        = Decision.ToCommit) :
    ∀ B_L ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks,
      isLeaderBlock system B_L → B_L.r = r →
      directDecide system (Beluga.Network.networkTraceWithPull system time k').base B_L
        ≠ Decision.Undecided := by
  sorry

/-! ### §D.2 Lemma 11 (eventual decision) -/

/-- Paper §D.2 Lemma 11: post-GST, any undecided leader block eventually
gets decided (non-`Undecided`). -/
theorem lemma11_eventual_decision
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i)
    (r : Round) (k₀ : ℕ) (h_gst : time k₀ ≥ system.GST) :
    ∃ k' ≥ k₀,
      (∀ B_L ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks,
        isLeaderBlock system B_L → B_L.r = r →
        directDecide system (Beluga.Network.networkTraceWithPull system time k').base B_L
          ≠ Decision.Undecided) := by
  obtain ⟨r₁, hr₁_ge, k', hk'_ge, h_committed⟩ :=
    three_consec_commit h_sync hN hHonest h_ids (r + 3) k₀ h_gst
  refine ⟨k', hk'_ge, ?_⟩
  exact backward_induction h_sync hN hHonest h_ids r r₁ k'
    (Nat.lt_of_succ_le hr₁_ge) h_committed

/-! ### §D.2 Lemma 12 — block accepted via `f+1`-references -/

/-- Paper §D.2 Lemma 12: post-GST, an honest validator with `f+1` honest
references for digest `d` eventually accepts `d`. -/
theorem lemma12_referenced_accepted
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h_sync : MysticetiBelugaSynchrony system time)
    (vid : ValidatorId) (d : BlockDigest) (k₀ : ℕ)
    (h_honest : isHonestValidator system vid = true)
    (h_gst : time k₀ ≥ system.GST)
    (h_available : ∃ honest_refs : List ValidatorId,
      honest_refs.length ≥ system.f + 1 ∧
      ∀ v ∈ honest_refs, isHonestValidator system v = true ∧
        ∃ B' ∈ (Beluga.Network.networkTraceWithPull system time k₀).base.blocks,
          B'.author = v ∧ B'.parents.contains d = true) :
    ∃ k' ≥ k₀, HasAccepted (Beluga.Network.networkTraceWithPull system time k').base vid d := by
  -- Step 1: extract any one honest referencer (the list has length ≥ f+1 ≥ 1).
  obtain ⟨honest_refs, h_count, h_props⟩ := h_available
  have h_nonempty : 0 < honest_refs.length := by
    have : 0 < system.f + 1 := Nat.succ_pos _
    omega
  obtain ⟨v, h_v_in⟩ : ∃ v, v ∈ honest_refs := by
    rcases honest_refs with _ | ⟨hd, tl⟩
    · simp at h_nonempty
    · exact ⟨hd, by simp⟩
  obtain ⟨_h_v_honest, B', h_B'_in, _h_B'_author, h_B'_refs⟩ := h_props v h_v_in
  -- Step 2: by `parent_blocks_in_pool`, the block with digest `d` is in the pool.
  obtain ⟨B_d, h_Bd_in, h_Bd_d⟩ :=
    h_sync.parent_blocks_in_pool k₀ B' d h_B'_in h_B'_refs
  -- Step 3: by `network_in_pool_eventually_accepted_withPull`, vid eventually
  -- has `hasAcceptedDigest B_d.d = true`.
  obtain ⟨k', hk'_le, h_acc_bool⟩ :=
    Beluga.Network.network_in_pool_eventually_accepted_withPull
      system time h_sync.timeMonotone h_sync.inPoolDelivery h_sync.acceptScheduling
      k₀ vid B_d h_honest h_gst h_Bd_in
  -- Step 4: `B_d.d = d`, so vid has accepted `d`. Convert Bool ↔ Prop.
  refine ⟨k', hk'_le, ?_⟩
  rw [← Beluga.Network.hasAcceptedDigest_iff_HasAccepted, ← h_Bd_d]
  exact h_acc_bool

/-! ### §D.2 Theorem 6 — consensus liveness -/

/-- Paper §D.2 Theorem 6: post-GST, transactions are eventually ordered
and finalized by every honest validator.

If an honest validator has accepted some block `B` at step `k` and
`tx ∈ B.payload`, then for every honest `vid_h` there is a step `k'`
at which `tx` appears in `vid_h`'s canonical transaction order. -/
theorem theorem6_consensus_liveness
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h_sync : MysticetiBelugaSynchrony system time)
    (hids : ValidIds system)
    (vid_acc : ValidatorId) (_h_acc_honest : isHonestValidator system vid_acc = true)
    (k : ℕ) (h_gst : time k ≥ system.GST)
    (B : Block) (h_B_in : B ∈ (Beluga.Network.networkTraceWithPull system time k).base.blocks)
    (_h_accepted : HasAccepted (Beluga.Network.networkTraceWithPull system time k).base vid_acc B.d)
    (tx : Transaction) (h_tx : tx ∈ B.payload)
    (vid_h : ValidatorId) (h_vid_h_honest : isHonestValidator system vid_h = true) :
    ∃ k', tx ∈ belugaTransactionOrderState
      (Beluga.Network.networkTraceWithPull system time k').base vid_h := by
  -- Step 1: by universal in-pool acceptance, vid_h eventually accepts B.d.
  obtain ⟨k', hk'_le, h_acc_bool⟩ :=
    Beluga.Network.network_in_pool_eventually_accepted_withPull
      system time h_sync.timeMonotone h_sync.inPoolDelivery h_sync.acceptScheduling
      k vid_h B h_vid_h_honest h_gst h_B_in
  refine ⟨k', ?_⟩
  -- Step 2: convert hasAcceptedDigest (Bool) to HasAccepted (Prop).
  have h_acc :
      HasAccepted (Beluga.Network.networkTraceWithPull system time k').base vid_h B.d := by
    rw [← Beluga.Network.hasAcceptedDigest_iff_HasAccepted]; exact h_acc_bool
  -- Step 3: B persists in the pool from k to k' by blocks-monotonicity.
  have h_B_in' :
      B ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks :=
    Beluga.Network.network_blocks_monotone_traceWithPull system time k k' hk'_le B h_B_in
  -- Step 4: the block_accept op for B.d is in emittedOperations at k'.
  have h_op_mem : ValidatorOperation.block_accept vid_h B.d ∈
      (Beluga.Network.networkTraceWithPull system time k').base.emittedOperations := h_acc
  -- Step 5: getBlockByDigest at k' returns some block B' with B'.d = B.d.
  -- Walk the order's flatMap: the block_accept op fires the branch.
  unfold belugaTransactionOrderState
  rw [List.mem_flatMap]
  refine ⟨.block_accept vid_h B.d, h_op_mem, ?_⟩
  -- Determine getBlockByDigest's output and show tx is in its payload.
  rcases h_some : getBlockByDigest
      (Beluga.Network.networkTraceWithPull system time k').base B.d with _ | B'
  · -- find? = none contradicts B ∈ blocks with B.d = B.d.
    exfalso
    unfold getBlockByDigest at h_some
    have h_no_match :
        ∀ b ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks,
          ¬ decide (b.d = B.d) = true := List.find?_eq_none.mp h_some
    have := h_no_match B h_B_in'
    simp at this
  · -- find? = some B'. The predicate at B' holds, so B'.d = B.d.
    -- By the bundle's `block_unique_by_digest` primitive (paper §D.3 item
    -- (iv)), B' = B, so B'.payload = B.payload and tx ∈ B'.payload.
    have h_mem : B' ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks := by
      unfold getBlockByDigest at h_some
      exact List.mem_of_find?_eq_some h_some
    have h_B'_d : B'.d = B.d := by
      unfold getBlockByDigest at h_some
      have := List.find?_some h_some
      simpa using this
    have h_eq : B' = B :=
      h_sync.block_unique_by_digest k' B' B h_mem h_B_in' h_B'_d
    simp only [h_some, h_eq]
    exact h_tx

end Liveness
end Mysticeti
end BlockSynchroniser
