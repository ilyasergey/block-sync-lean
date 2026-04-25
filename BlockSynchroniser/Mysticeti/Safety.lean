/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Mysticeti-Beluga safety bundle (paper Appendix D.3).

Status: theorem statements + paper proof sketches as docstrings.
Round 3c (Aristotle, project `47e91c18`) closed L14 fully and gave
structural proofs of L13, L16, T7 with bridge stubs documenting still-
needed protocol invariants. Round 2 fills L10 and the
`quorumIntersection` / `certified_unique` foundations. All five
lemmas below are pure quorum-intersection / pigeonhole arguments — no
timing model needed.
-/
import BlockSynchroniser.Block
import BlockSynchroniser.State
import BlockSynchroniser.System
import BlockSynchroniser.Causal
import BlockSynchroniser.Quorum
import BlockSynchroniser.Beluga.Patterns
import BlockSynchroniser.Mysticeti.Consensus

namespace BlockSynchroniser
namespace Mysticeti
namespace Safety

open Beluga

/-- `C` is a certificate for `B` if `C` is in round `B.r + 1`, references
`B` as a parent (so `B.d ∈ C.parents`), and both blocks are in the state.

Direct (round-`r+1`) certificate; the paper's broader notion includes
transitive references handled below via `Reaches`. -/
def isCertificateFor {S} [SystemState S] (state : S) (C B : Block) : Prop :=
  C.r = B.r + 1 ∧
  B.d ∈ C.parents ∧
  C ∈ SystemState.blocks state ∧
  B ∈ SystemState.blocks state

/--
**Lemma 10 (paper Appendix D.3).**
*The round-robin schedule of leader blocks in Mysticeti-Beluga ensures
that in any window of `3f + 3` consecutive rounds, there are three
consecutive rounds with honest leader blocks.*

The lemma assumes the standard BFT setup `n = 3f + 1` (the minimum
honest-majority size; the paper uses this implicitly throughout
Appendix D). A more general `n ≥ 3f + 1` version follows by the same
argument.

PROVIDED SOLUTION (paper Appendix D)
There are `3f + 1` groups of three consecutive rounds in any window of
`3f + 3` rounds (groups indexed by their starting offset, `0..3f`).
Due to the round-robin schedule (`leaderOf r := r % n`), each of the
`n = 3f + 1` validators is the leader of exactly 3 *positions* in the
3f+3 window when `n = 3f+1` (each validator appears in groups
indexed by 3 distinct starting offsets, modulo edge effects).

There are `2f + 1` honest validators (`n - f`). Each contributes 3
honest-position counts across the groups. Total honest contribution
is `3 · (2f + 1) = 6f + 3`. Distributed over `3f + 1` groups, the
average is `(6f + 3) / (3f + 1) > 2`, so by pigeonhole some group
must contain at least `⌈3 · (2f + 1) / (3f + 1)⌉ = 3` honest leaders
— i.e., all three rounds in that group have honest leaders.

Proof formalization requires Mathlib's `Finset.sum_le_card_nsmul`
or `Finset.exists_lt_of_sum_lt`. Queued for Aristotle round 2.
-/
theorem lemma10_round_robin_pigeonhole
    (system : BlockSynchroniserSystem) (startRound : Round)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length
                = 2 * system.f + 1) :
    ∃ r ≥ startRound, r + 2 < startRound + (3 * system.f + 3) ∧
      isHonestValidator system (leaderOf system r) = true ∧
      isHonestValidator system (leaderOf system (r + 1)) = true ∧
      isHonestValidator system (leaderOf system (r + 2)) = true := by
  sorry

/--
**Lemma 13 (paper Appendix D.3).**
*If `2f+1` round-`r` blocks from distinct validators are certificates of
a block `B` formed in round `r`, then every block in any round
`r' > r` must (directly or transitively) reference a certificate for
`B` formed in round `r`.*

PROVIDED SOLUTION (paper Appendix D)
Recall that a block is a certificate for `B` if it references `2f+1`
blocks that themselves reference `B`. Consider round `r+1`. Every
block in this round references `2f+1` blocks from round `r`. By quorum
intersection, any such set intersects the certificate set of `B` in at
least one honest validator. Since honest validators do not equivocate,
every round-`(r+1)` block must reference a block that is a certificate
for `B`. By induction over rounds, this property propagates to all
`r' > r`.
-/
theorem lemma13_cert_persistence
    (system : BlockSynchroniserSystem) {S} [SystemState S] (state : S)
    (h_no_eq : NoEquivocationInParents system state)
    (B : Block) (h_B : B ∈ SystemState.blocks state)
    (h_cert : ∃ certs : List Block,
                certs.length ≥ 2 * system.f + 1 ∧
                certs.Nodup ∧
                (certs.map (·.author)).Nodup ∧
                ∀ C ∈ certs, isCertificateFor state C B)
    (B' : Block) (h_in : B' ∈ SystemState.blocks state)
    (h_later : B'.r > B.r + 1) :
    ∃ C, isCertificateFor state C B ∧ Reaches state B' C := by
  obtain ⟨certs, h_len, h_nodup, h_auth_nodup, h_all_cert⟩ := h_cert
  -- Paper argument: strong induction on (B'.r − B.r − 1).
  -- Every block in round > B.r references ≥ 2f+1 blocks from the previous
  -- round (protocol DAG invariant). By Quorum.quorumIntersection, these
  -- parent sets always overlap the certificate set `certs`, so a certificate
  -- for B is transitively reachable.
  --
  -- Bridge: the DAG connectivity property (every block has a parent in the
  -- state in a strictly earlier round that itself reaches a cert for B, or
  -- IS a cert for B) is the core inductive invariant. It relies on
  -- protocol DAG structure + Quorum.quorumIntersection + h_no_eq.
  -- Queued for round 2 alongside quorumIntersection.
  have h_inductive_step :
      ∀ B'' : Block, B'' ∈ SystemState.blocks state → B''.r > B.r + 1 →
        ∃ C, isCertificateFor state C B ∧ Reaches state B'' C := by
    intro B'' h_in'' h_later''
    -- The proof proceeds by strong induction on B''.r.
    -- Base case (B''.r = B.r + 2): B'' has ≥ 2f+1 parents from round B.r+1.
    -- By Quorum.quorumIntersection with the cert authors, at least one parent
    -- is authored by an honest validator who also authored a cert in `certs`.
    -- By h_no_eq (NoEquivocationInParents), that parent IS the cert.
    -- So B'' directly references a certificate for B via Reaches.step.
    --
    -- Inductive step (B''.r > B.r + 2): B'' has a parent P in an earlier
    -- round. By IH, P reaches a cert for B. By Reaches.step, so does B''.
    --
    -- Both cases require the DAG structural property that blocks have
    -- ≥ 2f+1 parents from the previous round — this is the protocol
    -- invariant not yet formalized in SystemState. Queued for round 2.
    sorry
  exact h_inductive_step B' h_in h_later

/-
**Lemma 14 (paper Appendix D.3).**
*If an honest validator directly commits leader block `B_L^r`, then no
honest validator (directly or indirectly) decides to skip `B_L^r`.*
-/
theorem lemma14_no_skip
    (system : BlockSynchroniserSystem) {S} [SystemState S] (state : S)
    (view : ConsensusView)
    (B : Block) (h_direct_commit : directDecide system state B = Decision.ToCommit)
    (h_view_direct : ∀ vid, isHonestValidator system vid = true →
                       view vid B.d = directDecide system state B) :
    ∀ vid, isHonestValidator system vid = true →
      view vid B.d ≠ Decision.ToSkip := by
  -- By h_view_direct, every honest validator's view on B.d equals
  -- directDecide system state B = Decision.ToCommit (by h_direct_commit).
  -- Since Decision.ToCommit ≠ Decision.ToSkip, the conclusion follows.
  grind

/--
**Lemma 15 (paper Appendix D.3).**
*In Mysticeti-Beluga, at most one leader block can be certified for any
round `r`.*

This is a *specialization* of [`Beluga.certified_unique`](../Beluga/Patterns.lean):
restrict to leader blocks (where `author = leaderOf system r`), and
uniqueness follows.

PROVIDED SOLUTION (paper Appendix D)
Suppose two distinct leader blocks `B_{L1}^r` and `B_{L2}^r` both obtain
`2f+1` references from round `r+1`. By quorum intersection, at least
one honest validator must belong to both quorums, and thus would have
referenced both blocks in round `r`. This contradicts protocol rule
that a validator references at most one block per proposer round.
-/
theorem lemma15_unique_cert
    (system : BlockSynchroniserSystem) {S} [SystemState S] (state : S)
    (h_no_eq : NoEquivocationInParents system state)
    (B₁ B₂ : Block)
    (h_lead₁ : isLeaderBlock system B₁) (h_lead₂ : isLeaderBlock system B₂)
    (h_same_round : B₁.r = B₂.r)
    (h_cert₁ : certified system state B₁) (h_cert₂ : certified system state B₂) :
    B₁ = B₂ := by
  -- Specialization of Beluga.certified_unique: leader blocks share author by
  -- definition (both authored by leaderOf system B₁.r = leaderOf system B₂.r).
  have h_same_author : B₁.author = B₂.author := by
    unfold isLeaderBlock at h_lead₁ h_lead₂
    rw [h_lead₁, h_lead₂, h_same_round]
  exact certified_unique system state h_no_eq B₁ B₂ h_cert₁ h_cert₂ h_same_author h_same_round

/--
**Lemma 16 (paper Appendix D.3).**
*All honest validators decide a consistent status for each round leader
block.*

PROVIDED SOLUTION (paper Appendix D)
Consider two honest validators `v_i` and `v_j`, and let `n` be the
highest round in which `v_i` commits a leader block. We prove by
backward induction that for every round `x ≤ n`, both validators
assign the same status to `B_L^x`.

* Base case (x = n): validator `v_i` commits `B_L^n`. By Lemma 14,
  `v_j` cannot skip it and must also commit it. By Corollary 1 (no two
  honest validators commit distinct leader blocks in the same round),
  both commit the same block.
* Inductive step: assume the statement holds for all rounds in `(k, n]`.
  Consider round `k`. If either validator directly commits or directly
  skips `B_L^k`, the other must make the same decision by Lemma 11 and
  Lemma 14. Otherwise, both decisions are indirect and derived from a
  later committed leader. Let `k_i` and `k_j` be the rounds of the
  first such commits for `v_i` and `v_j` respectively. By the induction
  hypothesis, `k_i = k_j`, and both validators commit the same leader
  block. Since indirect decisions depend only on the causal history of
  that block, both validators derive the same decision for `B_L^k`.
-/
theorem lemma16_consistent_status
    (system : BlockSynchroniserSystem) {S} [SystemState S] (state : S)
    (view : ConsensusView)
    (h_view_direct : ∀ vid B, isHonestValidator system vid = true →
                       isLeaderBlock system B → B ∈ SystemState.blocks state →
                       directDecide system state B ≠ Decision.Undecided →
                       view vid B.d = directDecide system state B) :
    view.Consistent system := by
  -- Unfold consistency: for any digest d and honest validators vid₁, vid₂,
  -- if both have non-Undecided views on d, they must agree.
  intro d vid₁ vid₂ h_honest₁ h_honest₂ h_ne₁ h_ne₂
  -- Paper argument (backward induction):
  -- Each non-Undecided view decision traces back to a directDecide on some
  -- leader block (either directly, or indirectly via a committed later
  -- leader). When directDecide is non-Undecided, h_view_direct forces all
  -- honest validators to the same value. The backward induction in the
  -- paper additionally uses Lemma 14 (no skip of committed blocks) and
  -- Lemma 13 (certificate persistence) to handle the indirect case.
  --
  -- Bridge: if an honest validator's view on d is non-Undecided, there
  -- exists a leader block B with B.d = d in the state whose directDecide
  -- is non-Undecided. This captures the protocol invariant that all
  -- consensus decisions trace back to direct DAG-pattern observations.
  -- Queued for round 2 alongside the indirect-decision formalization.
  have h_exists_block : ∃ B, isLeaderBlock system B ∧
      B ∈ SystemState.blocks state ∧
      directDecide system state B ≠ Decision.Undecided ∧
      B.d = d := by
    sorry
  obtain ⟨B_w, h_leader, h_mem, h_dd, h_digest⟩ := h_exists_block
  have hv₁ := h_view_direct vid₁ B_w h_honest₁ h_leader h_mem h_dd
  have hv₂ := h_view_direct vid₂ B_w h_honest₂ h_leader h_mem h_dd
  rw [h_digest] at hv₁ hv₂
  rw [hv₁, hv₂]

/--
**Theorem 7 (paper Appendix D.3) — Mysticeti-Beluga consensus safety.**
*All honest validators order transactions consistently.*

PROVIDED SOLUTION (paper Appendix D)
By Lemma 16, all honest validators decide a consistent status for each
round leader block, meaning that all honest validators decide identical
`ToCommit` leader blocks. According to the consensus logic employed by
Mysticeti-Beluga, all honest validators will order `ToCommit` leader
blocks and their causal history blocks consistently. Therefore, for
transactions included in the ordered blocks, all honest validators
order them consistently.
-/
theorem theorem7_consensus_safety
    (system : BlockSynchroniserSystem) {S} [SystemState S] (state : S)
    (view : ConsensusView) (order : TransactionOrder)
    (h_view_consistent : view.Consistent system)
    (h_order_from_view :
      -- transaction ordering is derived consistently from the consensus
      -- view: if two honest validators have the same view, their orders
      -- are consistent prefixes of each other.
      ∀ vid₁ vid₂, isHonestValidator system vid₁ = true →
                   isHonestValidator system vid₂ = true →
                   (∀ d, view vid₁ d = view vid₂ d) →
                   (order vid₁).isPrefixOf (order vid₂) = true ∨
                   (order vid₂).isPrefixOf (order vid₁) = true) :
    order.Consistent system := by
  -- Paper argument: By Lemma 16, all honest validators assign identical
  -- decisions to each leader block. Combined with h_order_from_view
  -- (transaction ordering respects view equality), we obtain consistent
  -- transaction orders.
  intro vid₁ vid₂ h_honest₁ h_honest₂
  apply h_order_from_view vid₁ vid₂ h_honest₁ h_honest₂
  intro d
  -- From view consistency (Lemma 16): all honest validators assign the
  -- same status to each leader block. The full argument (paper Theorem 7)
  -- shows that consistent views imply *equal* views — a validator that
  -- has not yet decided a block will eventually decide it the same way as
  -- every other honest validator (by the backward induction of Lemma 16).
  --
  -- Bridge: decision completeness — if any honest validator has decided d,
  -- all honest validators eventually decide d (protocol liveness property).
  -- This upgrades ConsensusView.Consistent (no conflicting non-Undecided)
  -- to full view equality. Queued for round 2 alongside liveness proofs.
  have h_complete : view vid₁ d = Decision.Undecided ↔
      view vid₂ d = Decision.Undecided := by sorry
  by_cases h₁ : view vid₁ d = Decision.Undecided
  · rw [h₁, h_complete.mp h₁]
  · by_cases h₂ : view vid₂ d = Decision.Undecided
    · exact absurd (h_complete.mpr h₂) h₁
    · exact h_view_consistent d vid₁ vid₂ h_honest₁ h_honest₂ h₁ h₂

end Safety
end Mysticeti
end BlockSynchroniser
