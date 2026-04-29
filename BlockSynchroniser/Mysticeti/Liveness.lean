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

The §D.2 lemmas (L7–L11, T6) consume two paper-implicit per-action
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
      isHonestValidator system vid →
      time k ≥ system.GST →
      B ∈ (Beluga.Network.networkTraceWithPull system time k).base.blocks →
      B_L ∈ (Beluga.Network.networkTraceWithPull system time k).base.blocks →
      B.author = vid →
      isLeaderBlock system B_L →
      B_L.r + 1 = B.r →
      hasAcceptedDigest (Beluga.Network.networkTraceWithPull system time k).base vid B_L.d →
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
      B.parents.contains d →
      ∃ B_d ∈ (Beluga.Network.networkTraceWithPull system time k).base.blocks,
        B_d.d = d
  /-- Paper §3 (honest validator behavior): an honest validator
  proposes at most one block per round. Hence two blocks in the pool
  with the same honest author and the same round are equal. -/
  honest_block_uniqueness :
    ∀ (k : ℕ) (B B' : Block),
      B  ∈ (Beluga.Network.networkTraceWithPull system time k).base.blocks →
      B' ∈ (Beluga.Network.networkTraceWithPull system time k).base.blocks →
      isHonestValidator system B.author →
      B.author = B'.author →
      B.r = B'.r →
      B = B'


/-! ## §D.2 derived theorems

Each §D.2 lemma below takes `MysticetiBelugaSynchrony` plus the
standard BFT side conditions (`n = 3f + 1`, `|honest| = 2f + 1`,
contiguous IDs) and concludes against `networkBelugaTraceWithPull`. -/

/-- Helper: `eraseDups` preserves membership (mirrors the inline proof in
`Beluga.strongReferencerAuthors_mem`). -/
private lemma mem_of_mem_eraseDups {α : Type*} [BEq α] [LawfulBEq α] {a : α} :
    ∀ {l : List α}, a ∈ l.eraseDups → a ∈ l := by
  intro l hl
  induction l using List.reverseRecOn with
  | nil => simp at hl
  | append_singleton xs x ih =>
    simp_all +decide [List.eraseDups_append]
    grind +suggestions

/-- Helper: every member of `l` survives in `l.eraseDups`. -/
private lemma mem_eraseDups_of_mem {α : Type*} [BEq α] [LawfulBEq α] {a : α} :
    ∀ {l : List α}, a ∈ l → a ∈ l.eraseDups := by
  intro l hl
  induction l using List.reverseRecOn with
  | nil => simp at hl
  | append_singleton xs x ih =>
    rw [List.eraseDups_append]
    rw [List.mem_append] at hl
    rcases hl with h | h
    · exact List.mem_append_left _ (ih h)
    · simp at h
      subst h
      by_cases h_in : a ∈ xs
      · exact List.mem_append_left _ (ih h_in)
      · refine List.mem_append_right _ ?_
        have h_removeAll : [a].removeAll xs = [a] := by
          unfold List.removeAll
          simp [h_in]
        rw [h_removeAll, List.eraseDups_cons]
        simp

/-- Helper: `eraseDups` produces a duplicate-free list (uses
`Beluga.strongReferencerAuthors_nodup`'s loop-based reasoning). -/
private lemma list_eraseDups_nodup {α : Type*} [BEq α] [LawfulBEq α] :
    ∀ (l : List α), l.eraseDups.Nodup := by
  have h_loop_nodup :
      ∀ (l : List α) (acc : List α),
        List.Nodup acc →
          List.Nodup (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc) := by
    intros l acc hacc
    induction' l with hd tl ih generalizing acc <;>
      simp_all +decide [List.eraseDupsBy.loop]
    cases h : acc.any fun x2 => hd == x2 <;> simp_all +decide
    grind
  intro l
  exact h_loop_nodup _ _ (by simp +decide)

/-- Helper: `isCertificateBlockB` is monotone in trace blocks. If `B'`
is a certificate for `B` at step `k₁`, the same `B'` remains a
certificate at step `k₂ ≥ k₁` (its parent-references persist). -/
private lemma isCertificateBlockB_monotone
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (k₁ k₂ : ℕ) (h_le : k₁ ≤ k₂) (B B' : Block) :
    isCertificateBlockB system (Beluga.Network.networkTraceWithPull system time k₁).base B B'
        →
    isCertificateBlockB system (Beluga.Network.networkTraceWithPull system time k₂).base B B'
        := by
  intro h₁
  unfold isCertificateBlockB at *
  set blocks₁ := (Beluga.Network.networkTraceWithPull system time k₁).base.blocks
  set blocks₂ := (Beluga.Network.networkTraceWithPull system time k₂).base.blocks
  set pred : Block → Bool := fun P =>
    B'.parents.contains P.d && P.r == B.r + 1 && P.parents.contains B.d
  have h_blocks_sub : List.Subset blocks₁ blocks₂ := fun P h_in =>
    Beluga.Network.network_blocks_monotone_traceWithPull system time k₁ k₂ h_le P h_in
  have h_subset_authors :
      ((blocks₁.filter pred).map (·.author)).eraseDups.toFinset ⊆
      ((blocks₂.filter pred).map (·.author)).eraseDups.toFinset := by
    intro a h_a
    rw [List.mem_toFinset] at h_a ⊢
    have h_in₁ : a ∈ ((blocks₁.filter pred).map (·.author)) := mem_of_mem_eraseDups h_a
    rw [List.mem_map] at h_in₁
    obtain ⟨P, h_P_filter, h_P_eq⟩ := h_in₁
    rw [List.mem_filter] at h_P_filter
    apply mem_eraseDups_of_mem
    rw [List.mem_map]
    exact ⟨P, List.mem_filter.mpr ⟨h_blocks_sub h_P_filter.1, h_P_filter.2⟩, h_P_eq⟩
  have h_nodup₁ : ((blocks₁.filter pred).map (·.author)).eraseDups.Nodup :=
    list_eraseDups_nodup _
  have h_nodup₂ : ((blocks₂.filter pred).map (·.author)).eraseDups.Nodup :=
    list_eraseDups_nodup _
  have h_card_le :
      ((blocks₁.filter pred).map (·.author)).eraseDups.length ≤
      ((blocks₂.filter pred).map (·.author)).eraseDups.length := by
    rw [← List.toFinset_card_of_nodup h_nodup₁, ← List.toFinset_card_of_nodup h_nodup₂]
    exact Finset.card_le_card h_subset_authors
  have h₁' :
      ((blocks₁.filter pred).map (·.author)).eraseDups.length ≥ 2 * system.f + 1 := by
    simpa using h₁
  have h_len_ge : ((blocks₂.filter pred).map (·.author)).eraseDups.length ≥ 2 * system.f + 1 :=
    le_trans h₁' h_card_le
  simpa using h_len_ge

/-- Helper: `certificatePatternAtB` is monotone in the trace blocks.
Once the cert pattern holds at `k₁`, it continues to hold at
`k₂ ≥ k₁`. -/
private lemma certificatePatternAtB_monotone
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (k₁ k₂ : ℕ) (h_le : k₁ ≤ k₂) (B : Block) (atRound : Round) :
    certificatePatternAtB system (Beluga.Network.networkTraceWithPull system time k₁).base
        B atRound →
    certificatePatternAtB system (Beluga.Network.networkTraceWithPull system time k₂).base
        B atRound := by
  intro h₁
  unfold certificatePatternAtB at *
  set blocks₁ := (Beluga.Network.networkTraceWithPull system time k₁).base.blocks
  set blocks₂ := (Beluga.Network.networkTraceWithPull system time k₂).base.blocks
  set pred₁ : Block → Bool := fun B' => B'.r == atRound && isCertificateBlockB system
    (Beluga.Network.networkTraceWithPull system time k₁).base B B'
  set pred₂ : Block → Bool := fun B' => B'.r == atRound && isCertificateBlockB system
    (Beluga.Network.networkTraceWithPull system time k₂).base B B'
  have h_blocks_sub : List.Subset blocks₁ blocks₂ := fun B' h_in =>
    Beluga.Network.network_blocks_monotone_traceWithPull system time k₁ k₂ h_le B' h_in
  -- Each cert author at k₁ is a cert author at k₂.
  have h_subset_authors :
      ((blocks₁.filter pred₁).map (·.author)).eraseDups.toFinset ⊆
      ((blocks₂.filter pred₂).map (·.author)).eraseDups.toFinset := by
    intro a h_a
    rw [List.mem_toFinset] at h_a ⊢
    have h_in₁ : a ∈ ((blocks₁.filter pred₁).map (·.author)) := mem_of_mem_eraseDups h_a
    rw [List.mem_map] at h_in₁
    obtain ⟨B', h_B'_filter, h_B'_eq⟩ := h_in₁
    rw [List.mem_filter] at h_B'_filter
    obtain ⟨h_B'_in, h_B'_pred⟩ := h_B'_filter
    -- pred₁ B' = B'.r == atRound && isCertificateBlockB at k₁
    have h_round : B'.r == atRound := by
      have : pred₁ B' := h_B'_pred
      simp [pred₁] at this
      exact decide_eq_true this.1
    have h_cert₁ : isCertificateBlockB system
        (Beluga.Network.networkTraceWithPull system time k₁).base B B' := by
      have : pred₁ B' := h_B'_pred
      simp [pred₁] at this
      exact this.2
    -- Lift cert from k₁ to k₂.
    have h_cert₂ : isCertificateBlockB system
        (Beluga.Network.networkTraceWithPull system time k₂).base B B' :=
      isCertificateBlockB_monotone system time k₁ k₂ h_le B B' h_cert₁
    apply mem_eraseDups_of_mem
    rw [List.mem_map]
    refine ⟨B', ?_, h_B'_eq⟩
    rw [List.mem_filter]
    refine ⟨h_blocks_sub h_B'_in, ?_⟩
    show pred₂ B'
    simp [pred₂]
    exact ⟨by simpa using h_round, h_cert₂⟩
  have h_nodup₁ : ((blocks₁.filter pred₁).map (·.author)).eraseDups.Nodup :=
    list_eraseDups_nodup _
  have h_nodup₂ : ((blocks₂.filter pred₂).map (·.author)).eraseDups.Nodup :=
    list_eraseDups_nodup _
  have h_card_le :
      ((blocks₁.filter pred₁).map (·.author)).eraseDups.length ≤
      ((blocks₂.filter pred₂).map (·.author)).eraseDups.length := by
    rw [← List.toFinset_card_of_nodup h_nodup₁, ← List.toFinset_card_of_nodup h_nodup₂]
    exact Finset.card_le_card h_subset_authors
  have h₁' :
      ((blocks₁.filter pred₁).map (·.author)).eraseDups.length ≥ 2 * system.f + 1 := by
    simpa using h₁
  have h_len_ge : ((blocks₂.filter pred₂).map (·.author)).eraseDups.length ≥ 2 * system.f + 1 :=
    le_trans h₁' h_card_le
  simpa using h_len_ge

/-- Helper: bridge `(p.1, true) ∈ system.validators` to
`isHonestValidator system p.1 = true`. -/
private lemma isHonest_of_pair_mem
    (system : BlockSynchroniserSystem) (vid : ValidatorId)
    (h_mem : (vid, true) ∈ system.validators) :
    isHonestValidator system vid := by
  unfold isHonestValidator BlockSynchroniserSystem.isHonest
  have h_find : system.validators.find? (fun x => x.1 == vid) = some (vid, true) :=
    Beluga.Network.find?_of_mem_nodup _ vid true h_mem system.validatorsNodup
  have h_pred_eq :
      (fun (x : ValidatorId × Bool) => match x with | (vid_1, _) => decide (vid_1 = vid))
        = (fun x => x.1 == vid) := by
    funext x; cases x; show decide _ = (_ == _); rfl
  rw [h_pred_eq, h_find]

/-- Helper: the Byzantine-count bound — in any nodup list of
registered validator IDs, at most `f` entries are Byzantine. -/
private lemma byz_bound_of_system_constraints
    (system : BlockSynchroniserSystem)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2)).length
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
    (h_witness : ∃ vid_w bv_w, isHonestValidator system vid_w ∧
      (Beluga.Network.networkTraceWithPull system time k).base.getValidator vid_w = some bv_w ∧
      bv_w.currentRound = r) :
    ∃ k', k ≤ k' ∧ time k' ≤ time k + 4 * system.Δ ∧
      ∀ vid, isHonestValidator system vid →
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
    (h_honest : isHonestValidator system vid_leader)
    (_h_leader : vid_leader = leaderOf system r)
    (h_gst : time k ≥ system.GST)
    (h_witness : ∃ vid_w bv_w, isHonestValidator system vid_w ∧
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
          vid_leader bv_lead₁.currentRound
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
    (h_lead_honest : isHonestValidator system vid_leader)
    (h_ref_honest : isHonestValidator system vid_referencer)
    (h_leader : vid_leader = leaderOf system r)
    (h_gst : time k ≥ system.GST)
    (h_witness : ∃ vid_w bv_w, isHonestValidator system vid_w ∧
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
        vid_referencer (r + 1) :=
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

/-- Helper: given a fixed leader block `B_L`, iterate over a list of
validator-honesty pairs and accumulate, for each honest member, a
round-`(r+1)` block whose parents include `B_L.d`. The witness step
is the max of per-member witness steps; lifted via blocks-monotone. -/
private theorem honest_refs_for_validator_list
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h_sync : MysticetiBelugaSynchrony system time)
    (r : Round) (vid_leader : ValidatorId) (k_L : ℕ) (B_L : Block)
    (h_BL_in : B_L ∈ (Beluga.Network.networkTraceWithPull system time k_L).base.blocks)
    (_h_BL_author : B_L.author = vid_leader) (h_BL_round : B_L.r = r)
    (h_isLeader : isLeaderBlock system B_L)
    (h_post_gst_L : time k_L ≥ system.GST) :
    ∀ (vs : List (ValidatorId × Bool)),
      (∀ p ∈ vs, p.2 → isHonestValidator system p.1) →
      ∃ k', k_L ≤ k' ∧
        B_L ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks ∧
        ∀ p ∈ vs, p.2 →
          ∃ B ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks,
            B.author = p.1 ∧ B.r = r + 1 ∧ B_L.d ∈ B.parents := by
  intro vs
  induction vs with
  | nil =>
    intro _
    refine ⟨k_L, le_refl k_L, h_BL_in, ?_⟩
    intro p h_mem; simp at h_mem
  | cons hd tl ih =>
    intro h_premise
    have h_tl_premise : ∀ p ∈ tl, p.2 → isHonestValidator system p.1 :=
      fun p h_mem h_b => h_premise p (List.mem_cons_of_mem _ h_mem) h_b
    obtain ⟨k_t, hk_t_lo, h_BL_in_t, h_t⟩ := ih h_tl_premise
    by_cases h_hd_b : hd.2
    · -- hd is honest; derive its round-(r+1) block referencing B_L.
      have h_hd_honest : isHonestValidator system hd.1 :=
        h_premise hd List.mem_cons_self h_hd_b
      have h_post_gst_t : time k_t ≥ system.GST :=
        le_trans h_post_gst_L (h_sync.timeMonotone k_L k_t hk_t_lo)
      -- All honest reach round ≥ r+2 at some k_R ≥ k_t.
      obtain ⟨k_R, hk_R_lo, hk_R_gst, h_all_at_r2⟩ :=
        Beluga.Network.network_all_honest_eventually_at_roundWithPull
          system time h_sync.timeMonotone
          h_sync.networkDelivery h_sync.timeoutAdvance h_sync.boundedRoundSpread
          hd.1 h_hd_honest k_t h_post_gst_t (r + 2)
      obtain ⟨bv_hd, h_hd_get, h_hd_round⟩ := h_all_at_r2 hd.1 h_hd_honest
      -- hd has currentRound > r+1, so it has proposed for r+1.
      have h_hd_gt : r + 1 < bv_hd.currentRound :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self (r + 1)) h_hd_round
      have h_proposed :=
        Beluga.Network.network_proposed_for_lt_currentRoundWithPull
          system time k_R hd.1 bv_hd h_hd_get (r + 1) h_hd_gt
      -- Extract B_hd via the propose-op invariant.
      obtain ⟨B_hd, h_op⟩ :=
        Beluga.Network.hasProposedFor_implies_propose_op _ hd.1 (r + 1) h_proposed
      obtain ⟨h_hd_author, h_hd_r, _, h_hd_in⟩ :=
        Beluga.Network.network_propose_op_invariant_traceWithPull system time k_R
          hd.1 B_hd (r + 1) h_op
      -- B_L persists in pool at k_R.
      have h_BL_in_R :
          B_L ∈ (Beluga.Network.networkTraceWithPull system time k_R).base.blocks :=
        Beluga.Network.network_blocks_monotone_traceWithPull system time k_t k_R hk_R_lo
          B_L h_BL_in_t
      -- hd eventually accepts B_L; get the step k_acc.
      obtain ⟨k_acc, hk_acc_lo, h_acc_bool⟩ :=
        Beluga.Network.network_in_pool_eventually_accepted_withPull
          system time h_sync.timeMonotone h_sync.inPoolDelivery h_sync.acceptScheduling
          k_R hd.1 B_L h_hd_honest hk_R_gst h_BL_in_R
      -- Apply leader_inclusion at step k_acc.
      have h_BL_in_acc :
          B_L ∈ (Beluga.Network.networkTraceWithPull system time k_acc).base.blocks :=
        Beluga.Network.network_blocks_monotone_traceWithPull system time k_R k_acc hk_acc_lo
          B_L h_BL_in_R
      have h_hd_in_acc :
          B_hd ∈ (Beluga.Network.networkTraceWithPull system time k_acc).base.blocks :=
        Beluga.Network.network_blocks_monotone_traceWithPull system time k_R k_acc hk_acc_lo
          B_hd h_hd_in
      have h_post_gst_acc : time k_acc ≥ system.GST :=
        le_trans hk_R_gst (h_sync.timeMonotone k_R k_acc hk_acc_lo)
      have h_round_succ : B_L.r + 1 = B_hd.r := by rw [h_BL_round, h_hd_r]
      have h_BLd_in_parents : B_L.d ∈ B_hd.parents :=
        h_sync.leader_inclusion k_acc hd.1 B_hd B_L h_hd_honest h_post_gst_acc
          h_hd_in_acc h_BL_in_acc h_hd_author h_isLeader h_round_succ h_acc_bool
      -- Take k' = max k_t k_acc (already ≥ both).
      let k' := max k_t k_acc
      have hk'_lo_kt : k_t ≤ k' := le_max_left _ _
      have hk'_lo_kacc : k_acc ≤ k' := le_max_right _ _
      have hk'_lo_kL : k_L ≤ k' := le_trans hk_t_lo hk'_lo_kt
      have h_BL_in_k' : B_L ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks :=
        Beluga.Network.network_blocks_monotone_traceWithPull system time k_t k' hk'_lo_kt
          B_L h_BL_in_t
      refine ⟨k', hk'_lo_kL, h_BL_in_k', ?_⟩
      intro p h_mem h_p_b
      rw [List.mem_cons] at h_mem
      rcases h_mem with h_eq | h_in_t
      · -- p = hd.
        subst h_eq
        refine ⟨B_hd, ?_, h_hd_author, h_hd_r, h_BLd_in_parents⟩
        exact Beluga.Network.network_blocks_monotone_traceWithPull system time k_acc k' hk'_lo_kacc
          B_hd h_hd_in_acc
      · -- p ∈ tl: lift via monotonicity.
        obtain ⟨B_p, h_Bp_in, h_Bp_author, h_Bp_r, h_Bp_parents⟩ := h_t p h_in_t h_p_b
        refine ⟨B_p, ?_, h_Bp_author, h_Bp_r, h_Bp_parents⟩
        exact Beluga.Network.network_blocks_monotone_traceWithPull system time k_t k' hk'_lo_kt
          B_p h_Bp_in
    · -- hd is byzantine; the cons-case for hd is vacuous.
      refine ⟨k_t, hk_t_lo, h_BL_in_t, ?_⟩
      intro p h_mem h_p_b
      rw [List.mem_cons] at h_mem
      rcases h_mem with h_eq | h_in_t
      · subst h_eq; exact absurd h_p_b h_hd_b
      · exact h_t p h_in_t h_p_b

/-- Paper §D.2 Lemma 8: post-GST, the round-`r` honest leader's block
becomes `certified` (certificate pattern). -/
theorem honest_certify_leader
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h_sync : MysticetiBelugaSynchrony system time)
    (r : Round) (vid_leader : ValidatorId) (k : ℕ)
    (h_honest : isHonestValidator system vid_leader)
    (h_leader : vid_leader = leaderOf system r)
    (h_gst : time k ≥ system.GST)
    (h_witness : ∃ vid_w bv_w, isHonestValidator system vid_w ∧
      (Beluga.Network.networkTraceWithPull system time k).base.getValidator vid_w = some bv_w ∧
      bv_w.currentRound = r) :
    ∃ k', k ≤ k' ∧
      (∃ B_L ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks,
        isLeaderBlock system B_L ∧ B_L.r = r ∧
        certified system (Beluga.Network.networkTraceWithPull system time k').base B_L) := by
  -- Step 1: get B_L via leader_propose.
  obtain ⟨k_L, hk_L_lo, _, B_L, h_BL_in, h_BL_author, h_BL_round⟩ :=
    leader_propose h_sync r vid_leader k h_honest h_leader h_gst h_witness
  have h_post_gst_L : time k_L ≥ system.GST :=
    le_trans h_gst (h_sync.timeMonotone k k_L hk_L_lo)
  have h_isLeader : isLeaderBlock system B_L := by
    unfold isLeaderBlock
    rw [h_BL_author, h_leader, h_BL_round]
  -- Step 2: iterate over system.validators to gather honest references.
  have h_premise : ∀ p ∈ system.validators, p.2 → isHonestValidator system p.1 := by
    intro p h_mem h_b
    have h_pair : (p.1, true) ∈ system.validators := by
      rcases p with ⟨a, b⟩
      simp at h_b
      subst h_b
      exact h_mem
    exact isHonest_of_pair_mem system p.1 h_pair
  obtain ⟨k', hk'_lo, h_BL_in_k', h_refs⟩ :=
    honest_refs_for_validator_list h_sync r vid_leader k_L B_L h_BL_in h_BL_author h_BL_round
      h_isLeader h_post_gst_L system.validators h_premise
  -- Step 3: show `certified system state B_L` at k'.
  refine ⟨k', le_trans hk_L_lo hk'_lo, B_L, h_BL_in_k', h_isLeader, h_BL_round, ?_⟩
  unfold certified certificatePattern Beluga.strongReferencerAuthors
  set state := (Beluga.Network.networkTraceWithPull system time k').base
  -- The (after eraseDups) list of distinct referencer authors.
  set refAuthors :=
    ((state.blocks.filter (fun B' => decide (B_L.d ∈ B'.parents))).map (·.author)).eraseDups
  -- The (after-filter) list of honest validator IDs.
  set honestIds := (system.validators.filter (fun p => decide (p.2))).map Prod.fst
  -- Show honestIds.toFinset ⊆ refAuthors.toFinset.
  have h_subset : honestIds.toFinset ⊆ refAuthors.toFinset := by
    intro vid h_vid_in
    rw [List.mem_toFinset] at h_vid_in ⊢
    rw [List.mem_map] at h_vid_in
    obtain ⟨p, h_p_in_filter, h_p_eq⟩ := h_vid_in
    rw [List.mem_filter] at h_p_in_filter
    obtain ⟨h_p_in_v, h_p_b⟩ := h_p_in_filter
    have h_vid_b : p.2 := by simpa using h_p_b
    obtain ⟨B_p, h_Bp_in, h_Bp_author, _h_Bp_r, h_Bp_parents⟩ :=
      h_refs p h_p_in_v h_vid_b
    -- vid = p.1 = B_p.author.
    have h_vid_eq : vid = B_p.author := by rw [← h_p_eq, ← h_Bp_author]
    -- B_p.author ∈ (state.blocks.filter ...).map (·.author).
    have h_in_orig : B_p.author ∈
        (state.blocks.filter (fun B' => decide (B_L.d ∈ B'.parents))).map (·.author) := by
      rw [List.mem_map]
      refine ⟨B_p, ?_, rfl⟩
      rw [List.mem_filter]
      exact ⟨h_Bp_in, by simpa using h_Bp_parents⟩
    -- After eraseDups, B_p.author still appears.
    rw [h_vid_eq]
    exact mem_eraseDups_of_mem h_in_orig
  -- |honestIds.toFinset| ≥ 2f+1 from honestBound + nodup.
  have h_honest_nodup : honestIds.Nodup := by
    -- (l.filter p).map f is a sublist of l.map f.
    have h_sub :
        List.Sublist
          ((system.validators.filter (fun p => decide (p.2))).map Prod.fst)
          (system.validators.map Prod.fst) :=
      List.Sublist.map _ List.filter_sublist
    exact system.validatorsNodup.sublist h_sub
  have h_honest_card : honestIds.toFinset.card ≥ 2 * system.f + 1 := by
    rw [List.toFinset_card_of_nodup h_honest_nodup]
    show ((system.validators.filter (fun p => decide (p.2))).map Prod.fst).length
            ≥ 2 * system.f + 1
    rw [List.length_map]
    have h_filter_eq :
        (system.validators.filter (fun p => decide (p.2))).length =
        (system.validators.filter (fun p => p.2)).length := by
      apply congrArg List.length
      apply List.filter_congr
      intro p _; simp
    rw [h_filter_eq]
    exact system.honestBound
  -- |refAuthors.toFinset| ≥ |honestIds.toFinset| ≥ 2f+1 by subset.
  have h_refAuthors_card : refAuthors.toFinset.card ≥ 2 * system.f + 1 :=
    le_trans h_honest_card (Finset.card_le_card h_subset)
  -- |refAuthors| = |refAuthors.toFinset| (eraseDups makes it Nodup).
  have h_refAuthors_nodup : refAuthors.Nodup := list_eraseDups_nodup _
  have h_refAuthors_len_eq : refAuthors.length = refAuthors.toFinset.card :=
    (List.toFinset_card_of_nodup h_refAuthors_nodup).symm
  show refAuthors.length > 2 * system.f
  rw [h_refAuthors_len_eq]
  omega

/-! ### §D.2 Lemma 9 — round-robin pigeonhole

There are `3f + 1` groups of three consecutive rounds in any window
of `3f + 3` rounds. Due to the round-robin schedule, each of the
`2f + 1` honest validators appears in 3 such groups, contributing
`3 · (2f+1) = 6f+3` total honest-leader positions across `3f+1`
groups — average `> 2`, so by pigeonhole some group has 3 honest
leaders.
-/

/-- Combinatorial helper for `lemma9_round_robin_pigeonhole`.

In a circular sequence of length `n = 3f+1` with at most `f` "false"
positions, three consecutive "true" positions exist. Proved by
contradiction: each of the `n = 3f+1` triples `(i, i+1, i+2)` has a
false member; but each false position covers exactly 3 triples (by
the wrap-around), total coverage `3f < 3f+1`, contradiction.
-/
lemma consecutive_triple_exists (n f : Nat) (g : Nat → Bool)
    (hn : n = 3 * f + 1)
    (h_false_count : (Finset.range n |>.filter (fun i => g i = false)).card ≤ f)
    (h_wrap1 : g n = g 0) (h_wrap2 : g (n + 1) = g 1) :
    ∃ i, i < n ∧ g i ∧ g (i + 1) ∧ g (i + 2) := by
  have h_sum_ge : ∑ i ∈ Finset.range n, (if g i = false then 1 else 0)
      + ∑ i ∈ Finset.range n, (if g (i + 1) = false then 1 else 0)
      + ∑ i ∈ Finset.range n, (if g (i + 2) = false then 1 else 0) ≤ 3 * f := by
    have h_sum_ge : ∑ i ∈ Finset.range n, (if g (i + 1) = false then 1 else 0)
        = ∑ i ∈ Finset.range n, (if g i = false then 1 else 0) := by
      rcases n with (_ | _ | n) <;> simp_all +arith +decide [Finset.sum_range_succ']
      · simp_all +decide [Finset.filter_singleton]
      · rw [Finset.card_filter, Finset.card_filter]
        rw [Finset.sum_range_succ, Finset.sum_range_succ']; aesop
    have h_sum_ge : ∑ i ∈ Finset.range n, (if g (i + 2) = false then 1 else 0)
        = ∑ i ∈ Finset.range n, (if g i = false then 1 else 0) := by
      rcases n with (_ | _ | n) <;> simp_all +decide [Finset.sum_range_succ']
      · simp_all +decide [Finset.filter_singleton]
      · rw [Finset.card_filter, Finset.card_filter] at *
        rw [← h_sum_ge, Finset.sum_range_succ, Finset.sum_range_succ']; aesop
    simp_all +arith +decide [Finset.sum_ite]
  contrapose! h_sum_ge
  have h_sum_ge : ∀ i < n, (if g i = false then 1 else 0)
      + (if g (i + 1) = false then 1 else 0)
      + (if g (i + 2) = false then 1 else 0) ≥ 1 := by grind
  simpa only [← Finset.sum_add_distrib] using
    lt_of_lt_of_le (by norm_num [hn])
      (Finset.sum_le_sum fun i hi => h_sum_ge i (Finset.mem_range.mp hi))

/-- **Lemma 9 (paper Appendix D.2).**

> *The round-robin schedule of leader blocks in Mysticeti-Beluga
> ensures that in any window of `3f + 3` rounds, there are three
> consecutive rounds with honest leader blocks.*

Paper proof sketch: there are `3f + 1` groups of three consecutive
rounds in any window of `3f + 3` rounds. Due to the round-robin
schedule, each of the `2f + 1` honest validators is one of the
leaders in exactly 3 such groups. Total honest-leader positions:
`3 · (2f+1) = 6f+3` across `3f+1` groups; by pigeonhole some group
contains `⌈(6f+3)/(3f+1)⌉ = 3` honest leader blocks.

The Lean statement returns the explicit start round of the
consecutive-honest triple. -/
theorem lemma9_round_robin_pigeonhole
    (system : BlockSynchroniserSystem) (startRound : Round)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2)).length
                = 2 * system.f + 1)
    -- Validator IDs are {0, ..., n-1}, matching the round-robin's
    -- `r % n` output. Without this, `leaderOf` could produce IDs that
    -- don't correspond to any registered validator, making
    -- `isHonestValidator` return `false` for all leaders.
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i) :
    ∃ r ≥ startRound, r + 2 < startRound + (3 * system.f + 3) ∧
      isHonestValidator system (leaderOf system r) ∧
      isHonestValidator system (leaderOf system (r + 1)) ∧
      isHonestValidator system (leaderOf system (r + 2)) := by
  have h_pigeonhole : ∃ i < system.n,
      isHonestValidator system (leaderOf system (startRound + i)) ∧
      isHonestValidator system (leaderOf system (startRound + i + 1)) ∧
      isHonestValidator system (leaderOf system (startRound + i + 2)) := by
    have := consecutive_triple_exists (3 * system.f + 1) system.f
        (fun i => isHonestValidator system ((startRound + i) % (3 * system.f + 1)))
        rfl ?_ ?_ ?_
    · unfold leaderOf; aesop
    · have h_false_count : (Finset.range (3 * system.f + 1)
          |>.filter (fun i => isHonestValidator system i = false)).card ≤ system.f := by
        have h_false_count : (Finset.filter (fun i => isHonestValidator system i = false)
            (Finset.range (3 * system.f + 1))).card
            ≤ (system.validators.filter (fun p => p.2 = false)).length := by
          have h_false_count : Finset.filter (fun i => isHonestValidator system i = false)
              (Finset.range (3 * system.f + 1))
              ⊆ Finset.image (fun p => p.1) (List.toFinset
                  (List.filter (fun p => p.2 = false) system.validators)) := by
            intro i hi
            simp_all +decide [isHonestValidator]
            cases h_ids i hi.1 <;> simp_all +decide [BlockSynchroniserSystem.isHonest]
            cases h : List.find? (fun x => decide (x.1 = i)) system.validators <;>
              simp_all +decide [List.find?_eq_none]
            · exact False.elim <| h i |>.2 ‹_› rfl
            · grind
          exact le_trans (Finset.card_le_card h_false_count)
            (Finset.card_image_le.trans (List.toFinset_card_le _))
        have h_false_count : (system.validators.filter (fun p => p.2)).length
            + (system.validators.filter (fun p => p.2 = false)).length = system.n := by
          have h_false_count : ∀ (l : List (ValidatorId × Bool)),
              (l.filter (fun p => p.2)).length
              + (l.filter (fun p => p.2 = false)).length = l.length := by
            intro l; induction l <;> simp +decide [*]; grind
          rw [h_false_count, system.validatorCountCorrect]
        grind
      convert h_false_count using 1
      refine Finset.card_bij (fun i _ => (startRound + i) % (3 * system.f + 1)) ?_ ?_ ?_ <;>
        simp +decide [Nat.mod_lt]
      · exact fun a _ ha' => ⟨Nat.le_of_lt_succ <| Nat.mod_lt _ <| Nat.succ_pos _, ha'⟩
      · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h
        have := Nat.modEq_iff_dvd.mp h.symm
        simp_all +decide [Nat.dvd_iff_mod_eq_zero]
        obtain ⟨k, hk⟩ := this; nlinarith [show k = 0 by nlinarith]
      · intro b hb hb'
        use (b + (3 * system.f + 1) - startRound % (3 * system.f + 1)) % (3 * system.f + 1)
        simp +decide [← ZMod.val_natCast,
          Nat.cast_sub (show startRound % (3 * system.f + 1) ≤ b + (3 * system.f + 1) from
            le_trans (Nat.mod_lt _ (Nat.succ_pos _) |> Nat.le_of_lt) (Nat.le_add_left _ _))]
        simp +decide [Nat.cast_sub (show (startRound : ℕ) % (3 * system.f + 1)
            ≤ b + (3 * system.f + 1) from
            le_trans (Nat.mod_lt _ (Nat.succ_pos _) |> Nat.le_of_lt) (Nat.le_add_left _ _))]
        exact ⟨⟨Nat.le_of_lt_succ <| by exact ZMod.val_lt _,
              by simpa [Nat.mod_eq_of_lt (show b < 3 * system.f + 1 from
                Nat.lt_succ_of_le hb)] using hb'⟩, hb⟩
    · norm_num [Nat.mod_eq_of_lt]
    · simp +decide [← hN, Nat.mod_eq_of_lt]
      norm_num [add_assoc, Nat.add_mod]
  grind

/-! ### Direct commit for an honest leader (helper for §D.2) -/

/-- Direct-commit helper: given an honest leader at round `r`, post-GST,
there is a future step `k'` and a leader block `B_L` at round `r` whose
`directDecide` is `Decision.ToCommit`.

Bypasses `honest_certify_leader`'s `bv_w.currentRound = r` witness
constraint by chaining `network_all_honest_eventually_at_roundWithPull`
(advance to `R = r + 1`) with `network_proposed_for_lt_currentRoundWithPull`
(extract the leader's propose-op for `r`), then iterating
`honest_refs_for_validator_list` to gather the cert-pattern referencers,
then closing via `cert_pattern_at_r2` and the `directDecide` body. -/
private theorem direct_commit_for_honest_leader
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h_sync : MysticetiBelugaSynchrony system time)
    (r : Round) (k₀ : ℕ) (h_gst : time k₀ ≥ system.GST)
    (h_honest_leader : isHonestValidator system (leaderOf system r)) :
    ∃ k' ≥ k₀, ∃ B_L ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks,
      B_L.author = leaderOf system r ∧ B_L.r = r ∧
      directDecide system (Beluga.Network.networkTraceWithPull system time k').base B_L
        = Decision.ToCommit := by
  -- Step 1: advance all honest validators to currentRound ≥ r + 1.
  obtain ⟨k_W, hk_W_lo, hk_W_gst, h_at⟩ :=
    Beluga.Network.network_all_honest_eventually_at_roundWithPull
      system time h_sync.timeMonotone
      h_sync.networkDelivery h_sync.timeoutAdvance h_sync.boundedRoundSpread
      (leaderOf system r) h_honest_leader k₀ h_gst (r + 1)
  obtain ⟨bv_lead, h_lead_get, h_lead_round⟩ := h_at (leaderOf system r) h_honest_leader
  -- Step 2: leader has currentRound > r, so it has proposed for r.
  have h_lead_gt : r < bv_lead.currentRound := h_lead_round
  have h_proposed :=
    Beluga.Network.network_proposed_for_lt_currentRoundWithPull
      system time k_W (leaderOf system r) bv_lead h_lead_get r h_lead_gt
  -- Step 3: extract B_L via the propose-op invariant.
  obtain ⟨B_L, h_op⟩ :=
    Beluga.Network.hasProposedFor_implies_propose_op _ (leaderOf system r) r h_proposed
  obtain ⟨h_BL_author, h_BL_round, _h_BL_digest, h_BL_in⟩ :=
    Beluga.Network.network_propose_op_invariant_traceWithPull system time k_W
      (leaderOf system r) B_L r h_op
  have h_isLeader : isLeaderBlock system B_L := by
    unfold isLeaderBlock; rw [h_BL_author, h_BL_round]
  -- Step 4: gather 2f+1 honest references via the iteration helper.
  have h_premise : ∀ p ∈ system.validators, p.2 → isHonestValidator system p.1 := by
    intro p h_mem h_b
    have h_pair : (p.1, true) ∈ system.validators := by
      rcases p with ⟨a, b⟩
      simp at h_b
      subst h_b
      exact h_mem
    exact isHonest_of_pair_mem system p.1 h_pair
  obtain ⟨k', hk'_lo, h_BL_in_k', h_refs⟩ :=
    honest_refs_for_validator_list h_sync r (leaderOf system r) k_W B_L h_BL_in
      h_BL_author h_BL_round h_isLeader hk_W_gst system.validators h_premise
  refine ⟨k', le_trans hk_W_lo hk'_lo, B_L, h_BL_in_k', h_BL_author, h_BL_round, ?_⟩
  -- Step 5: show directDecide returns ToCommit.
  set state := (Beluga.Network.networkTraceWithPull system time k').base with h_state
  have h_post_gst' : time k' ≥ system.GST :=
    le_trans hk_W_gst (h_sync.timeMonotone k_W k' hk'_lo)
  -- Show certified at k'.
  have h_certified : certified system state B_L := by
    unfold certified certificatePattern Beluga.strongReferencerAuthors
    set refAuthors :=
      ((state.blocks.filter (fun B' => decide (B_L.d ∈ B'.parents))).map (·.author)).eraseDups
    set honestIds := (system.validators.filter (fun p => decide (p.2))).map Prod.fst
    have h_subset : honestIds.toFinset ⊆ refAuthors.toFinset := by
      intro vid h_vid_in
      rw [List.mem_toFinset] at h_vid_in ⊢
      rw [List.mem_map] at h_vid_in
      obtain ⟨p, h_p_in_filter, h_p_eq⟩ := h_vid_in
      rw [List.mem_filter] at h_p_in_filter
      obtain ⟨h_p_in_v, h_p_b⟩ := h_p_in_filter
      have h_vid_b : p.2 := by simpa using h_p_b
      obtain ⟨B_p, h_Bp_in, h_Bp_author, _h_Bp_r, h_Bp_parents⟩ :=
        h_refs p h_p_in_v h_vid_b
      have h_vid_eq : vid = B_p.author := by rw [← h_p_eq, ← h_Bp_author]
      have h_in_orig : B_p.author ∈
          (state.blocks.filter (fun B' => decide (B_L.d ∈ B'.parents))).map (·.author) := by
        rw [List.mem_map]
        refine ⟨B_p, ?_, rfl⟩
        rw [List.mem_filter]
        exact ⟨h_Bp_in, by simpa using h_Bp_parents⟩
      rw [h_vid_eq]
      exact mem_eraseDups_of_mem h_in_orig
    have h_honest_nodup : honestIds.Nodup := by
      have h_sub :
          List.Sublist
            ((system.validators.filter (fun p => decide (p.2))).map Prod.fst)
            (system.validators.map Prod.fst) :=
        List.Sublist.map _ List.filter_sublist
      exact system.validatorsNodup.sublist h_sub
    have h_honest_card : honestIds.toFinset.card ≥ 2 * system.f + 1 := by
      rw [List.toFinset_card_of_nodup h_honest_nodup]
      show ((system.validators.filter (fun p => decide (p.2))).map Prod.fst).length
              ≥ 2 * system.f + 1
      rw [List.length_map]
      have h_filter_eq :
          (system.validators.filter (fun p => decide (p.2))).length =
          (system.validators.filter (fun p => p.2)).length := by
        apply congrArg List.length
        apply List.filter_congr
        intro p _; simp
      rw [h_filter_eq]
      exact system.honestBound
    have h_refAuthors_card : refAuthors.toFinset.card ≥ 2 * system.f + 1 :=
      le_trans h_honest_card (Finset.card_le_card h_subset)
    have h_refAuthors_nodup : refAuthors.Nodup := list_eraseDups_nodup _
    have h_refAuthors_len_eq : refAuthors.length = refAuthors.toFinset.card :=
      (List.toFinset_card_of_nodup h_refAuthors_nodup).symm
    show refAuthors.length > 2 * system.f
    rw [h_refAuthors_len_eq]
    omega
  -- Now apply cert_pattern_at_r2 + directDecide unfolding.
  have h_cert : certificatePatternAtB system state B_L (B_L.r + 2) :=
    h_sync.cert_pattern_at_r2 k' B_L h_post_gst' h_BL_in_k' h_isLeader h_certified
  unfold directDecide
  rw [h_cert]
  rfl

/-! ### Three consecutive direct commits (helper for §D.2) -/

/-- Helper for §D.2 (proof of Lemma 10): with three consecutive
honest leaders, their leader blocks all direct-commit `ToCommit`.

Concretely: there is a future step `k'` and a starting round `r₁ ≥
startRound` such that for every leader block `B_L` in the pool at `k'`
whose round is `r₁`, `r₁+1`, or `r₁+2`, `directDecide` returns
`Decision.ToCommit`. The universal-over-`B_L` form is mechanically
sound because the round bracket pins blocks to honest authors (via the
round-robin schedule and `lemma9_round_robin_pigeonhole`), and
`honest_block_uniqueness` collapses any two leader blocks at the same
honest-authored round to the same block. -/
theorem three_consec_commit
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2)).length = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i)
    (startRound : Round) (k₀ : ℕ) (h_gst : time k₀ ≥ system.GST) :
    ∃ r₁ ≥ startRound, ∃ k' ≥ k₀,
      (∀ B_L ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks,
        isLeaderBlock system B_L →
        (B_L.r = r₁ ∨ B_L.r = r₁ + 1 ∨ B_L.r = r₁ + 2) →
        directDecide system (Beluga.Network.networkTraceWithPull system time k').base B_L
          = Decision.ToCommit) := by
  -- Step 1: lemma10 → r₁ ≥ startRound with three consecutive honest leaders.
  obtain ⟨r₁, hr₁_ge, _hr₁_lt, h_hon₀, h_hon₁, h_hon₂⟩ :=
    lemma9_round_robin_pigeonhole system startRound hN hHonest h_ids
  refine ⟨r₁, hr₁_ge, ?_⟩
  -- Step 2: derive committed leader blocks at each of the three rounds.
  obtain ⟨k_a, hk_a_lo, B_a, hB_a_in, hB_a_author, hB_a_round, hB_a_commit⟩ :=
    direct_commit_for_honest_leader h_sync r₁ k₀ h_gst h_hon₀
  have h_gst_a : time k_a ≥ system.GST := le_trans h_gst (h_sync.timeMonotone k₀ k_a hk_a_lo)
  obtain ⟨k_b, hk_b_lo, B_b, hB_b_in, hB_b_author, hB_b_round, hB_b_commit⟩ :=
    direct_commit_for_honest_leader h_sync (r₁ + 1) k_a h_gst_a h_hon₁
  have h_gst_b : time k_b ≥ system.GST := le_trans h_gst_a (h_sync.timeMonotone k_a k_b hk_b_lo)
  obtain ⟨k_c, hk_c_lo, B_c, hB_c_in, hB_c_author, hB_c_round, hB_c_commit⟩ :=
    direct_commit_for_honest_leader h_sync (r₁ + 2) k_b h_gst_b h_hon₂
  -- Step 3: take k' = k_c and lift everything to k_c via blocks/cert monotonicity.
  refine ⟨k_c, le_trans hk_a_lo (le_trans hk_b_lo hk_c_lo), ?_⟩
  -- B_a, B_b are at k_a, k_b; need cert-pattern monotonicity to lift to k_c.
  -- directDecide at k_a returns ToCommit, hence certificatePatternAtB holds at k_a.
  have hk_a_le_c : k_a ≤ k_c := le_trans hk_b_lo hk_c_lo
  have hk_b_le_c : k_b ≤ k_c := hk_c_lo
  have hB_a_in_c : B_a ∈ (Beluga.Network.networkTraceWithPull system time k_c).base.blocks :=
    Beluga.Network.network_blocks_monotone_traceWithPull system time k_a k_c hk_a_le_c B_a hB_a_in
  have hB_b_in_c : B_b ∈ (Beluga.Network.networkTraceWithPull system time k_c).base.blocks :=
    Beluga.Network.network_blocks_monotone_traceWithPull system time k_b k_c hk_b_le_c B_b hB_b_in
  -- Lift cert-pattern from k_a to k_c.
  have hB_a_cert_a : certificatePatternAtB system
      (Beluga.Network.networkTraceWithPull system time k_a).base B_a (B_a.r + 2) := by
    have := hB_a_commit
    unfold directDecide at this
    by_cases h : certificatePatternAtB system
        (Beluga.Network.networkTraceWithPull system time k_a).base B_a (B_a.r + 2)
    · exact h
    · push_neg at h
      simp [Bool.not_eq_true] at h
      rw [h] at this
      split_ifs at this <;> simp_all
  have hB_b_cert_b : certificatePatternAtB system
      (Beluga.Network.networkTraceWithPull system time k_b).base B_b (B_b.r + 2) := by
    have := hB_b_commit
    unfold directDecide at this
    by_cases h : certificatePatternAtB system
        (Beluga.Network.networkTraceWithPull system time k_b).base B_b (B_b.r + 2)
    · exact h
    · push_neg at h
      simp [Bool.not_eq_true] at h
      rw [h] at this
      split_ifs at this <;> simp_all
  have hB_a_cert_c :
      certificatePatternAtB system (Beluga.Network.networkTraceWithPull system time k_c).base
        B_a (B_a.r + 2) :=
    certificatePatternAtB_monotone system time k_a k_c hk_a_le_c B_a (B_a.r + 2) hB_a_cert_a
  have hB_b_cert_c :
      certificatePatternAtB system (Beluga.Network.networkTraceWithPull system time k_c).base
        B_b (B_b.r + 2) :=
    certificatePatternAtB_monotone system time k_b k_c hk_b_le_c B_b (B_b.r + 2) hB_b_cert_b
  -- Now prove the universal claim.
  intro B_L hB_L_in hB_L_leader hB_L_round
  -- Show B_L equals one of B_a, B_b, B_c (via honest_block_uniqueness).
  have h_leader_eq : B_L.author = leaderOf system B_L.r := hB_L_leader
  rcases hB_L_round with hr | hr | hr
  · -- B_L.r = r₁; B_L.author = leaderOf r₁ = B_a.author.
    have h_authors_eq : B_L.author = B_a.author := by
      rw [h_leader_eq, hr, ← hB_a_author]
    have h_rounds_eq : B_L.r = B_a.r := by rw [hr, hB_a_round]
    have h_eq : B_L = B_a := by
      apply h_sync.honest_block_uniqueness k_c B_L B_a hB_L_in hB_a_in_c
      · rw [h_authors_eq]; rw [hB_a_author]; exact h_hon₀
      · exact h_authors_eq
      · exact h_rounds_eq
    rw [h_eq]
    -- directDecide for B_a at k_c is ToCommit (by cert at k_c).
    unfold directDecide
    rw [hB_a_cert_c]
    rfl
  · have h_authors_eq : B_L.author = B_b.author := by
      rw [h_leader_eq, hr, ← hB_b_author]
    have h_rounds_eq : B_L.r = B_b.r := by rw [hr, hB_b_round]
    have h_eq : B_L = B_b := by
      apply h_sync.honest_block_uniqueness k_c B_L B_b hB_L_in hB_b_in_c
      · rw [h_authors_eq]; rw [hB_b_author]; exact h_hon₁
      · exact h_authors_eq
      · exact h_rounds_eq
    rw [h_eq]
    unfold directDecide
    rw [hB_b_cert_c]
    rfl
  · have h_authors_eq : B_L.author = B_c.author := by
      rw [h_leader_eq, hr, ← hB_c_author]
    have h_rounds_eq : B_L.r = B_c.r := by rw [hr, hB_c_round]
    have h_eq : B_L = B_c := by
      apply h_sync.honest_block_uniqueness k_c B_L B_c hB_L_in hB_c_in
      · rw [h_authors_eq]; rw [hB_c_author]; exact h_hon₂
      · exact h_authors_eq
      · exact h_rounds_eq
    rw [h_eq]
    exact hB_c_commit

/-! ### §D.2 Lemma 10 (existential eventual commit) -/

/-- Paper §D.2 Lemma 10 (existential corollary of `three_consec_commit`):
post-GST, there is a future state at which some leader block at some
round `≥ startRound` is direct-committed.

The paper's full §D.2 L10 ("every leader's decision is eventually
decided") additionally invokes the §D.1.1 indirect-decision rule to
chain decisions backward through committed leaders; that recursion
needs `indirectDecideStep`-level mechanization which is deferred.
Theorem 6 (`theorem6_consensus_liveness`) below does not use the
backward chain — it draws acceptance propagation directly from §5
in-pool delivery and §4.2 accept-action liveness. -/
theorem lemma10_eventual_commit
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2)).length = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i)
    (startRound : Round) (k₀ : ℕ) (h_gst : time k₀ ≥ system.GST) :
    ∃ r₁ ≥ startRound, ∃ k' ≥ k₀,
      ∃ B_L ∈ (Beluga.Network.networkTraceWithPull system time k').base.blocks,
        isLeaderBlock system B_L ∧ B_L.r = r₁ ∧
        directDecide system (Beluga.Network.networkTraceWithPull system time k').base B_L
          = Decision.ToCommit := by
  -- Use lemma10 → r₁; then extract B_L via direct_commit_for_honest_leader.
  obtain ⟨r₁, hr₁_ge, _hr₁_lt, h_hon₀, _, _⟩ :=
    lemma9_round_robin_pigeonhole system startRound hN hHonest h_ids
  obtain ⟨k', hk'_lo, B_L, hB_L_in, hB_L_author, hB_L_round, hB_L_commit⟩ :=
    direct_commit_for_honest_leader h_sync r₁ k₀ h_gst h_hon₀
  refine ⟨r₁, hr₁_ge, k', hk'_lo, B_L, hB_L_in, ?_, hB_L_round, hB_L_commit⟩
  unfold isLeaderBlock; rw [hB_L_author, hB_L_round]

/-! ### §D.2 Lemma 11 — block accepted via `f+1`-references -/

/-- Paper §D.2 Lemma 11: post-GST, an honest validator with `f+1` honest
references for digest `d` eventually accepts `d`. -/
theorem lemma11_referenced_accepted
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h_sync : MysticetiBelugaSynchrony system time)
    (vid : ValidatorId) (d : BlockDigest) (k₀ : ℕ)
    (h_honest : isHonestValidator system vid)
    (h_gst : time k₀ ≥ system.GST)
    (h_available : ∃ honest_refs : List ValidatorId,
      honest_refs.length ≥ system.f + 1 ∧
      ∀ v ∈ honest_refs, isHonestValidator system v ∧
        ∃ B' ∈ (Beluga.Network.networkTraceWithPull system time k₀).base.blocks,
          B'.author = v ∧ B'.parents.contains d) :
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
    (vid_acc : ValidatorId) (_h_acc_honest : isHonestValidator system vid_acc)
    (k : ℕ) (h_gst : time k ≥ system.GST)
    (B : Block) (h_B_in : B ∈ (Beluga.Network.networkTraceWithPull system time k).base.blocks)
    (_h_accepted : HasAccepted (Beluga.Network.networkTraceWithPull system time k).base vid_acc B.d)
    (tx : Transaction) (h_tx : tx ∈ B.payload)
    (vid_h : ValidatorId) (h_vid_h_honest : isHonestValidator system vid_h) :
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
          ¬ decide (b.d = B.d) := List.find?_eq_none.mp h_some
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
