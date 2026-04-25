/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Mysticeti-Beluga safety bundle (paper Appendix D.3).

Status: theorem statements + paper proof sketches as docstrings; proofs
are `sorry` for delegation to Aristotle (Phase 6 stretch). All five
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
  sorry

/--
**Lemma 14 (paper Appendix D.3).**
*If an honest validator directly commits leader block `B_L^r`, then no
honest validator (directly or indirectly) decides to skip `B_L^r`.*

PROVIDED SOLUTION (paper Appendix D)
Assume for contradiction that some honest validator commits `B_L^r`
while another skips it.
* If `B_L^r` is *directly* skipped: a direct skip occurs only if at
  most `f` round `r+1` blocks reference `B_L^r`. However, if `B_L^r` is
  committed, then by the decision rule, at least `2f+1` round `r+1`
  blocks reference it. Any conflicting observation would violate quorum
  intersection, implying a single honest validator equivocated in round
  `r+1`, a contradiction.
* If `B_L^r` is *indirectly* skipped via some later leader `B_L^{r''}`
  with `r'' > r+2`: the skip must arise because `B_L^{r''}` does not
  reference a certificate for `B_L^r`. However, since `B_L^r` is
  directly committed, it has `2f+1` certificates formed by distinct
  validators in round `r+1`. By Lemma 13, a certificate for `B_L^r`
  must be referenced by all future blocks. This contradiction completes
  the proof.
-/
theorem lemma14_no_skip
    (system : BlockSynchroniserSystem) {S} [SystemState S] (state : S)
    (view : ConsensusView)
    (B : Block) (h_direct_commit : directDecide system state B = Decision.ToCommit)
    (h_view_direct : ∀ vid, isHonestValidator system vid = true →
                       view vid B.d = directDecide system state B) :
    ∀ vid, isHonestValidator system vid = true →
      view vid B.d ≠ Decision.ToSkip := by
  sorry

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
  sorry

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
  sorry

end Safety
end Mysticeti
end BlockSynchroniser
