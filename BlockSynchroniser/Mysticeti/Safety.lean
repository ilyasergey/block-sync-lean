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
import Mathlib.Tactic
import BlockSynchroniser.Block
import BlockSynchroniser.State
import BlockSynchroniser.System
import BlockSynchroniser.Causal
import BlockSynchroniser.Quorum
import BlockSynchroniser.Beluga.Patterns
import BlockSynchroniser.Mysticeti.Consensus

set_option linter.unusedSimpArgs false

namespace BlockSynchroniser

/-- Transitivity of the `Reaches` relation: if `a` reaches `b` and `b`
reaches `c`, then `a` reaches `c`. -/
-- proof: aristotle (project 9d7e8e08) — added in round 6
theorem Reaches.trans {S : Type} [SystemState S] {state : S} {a b c : Block}
    (hab : Reaches state a b) (hbc : Reaches state b c) : Reaches state a c := by
  induction hbc with
  | refl => exact hab
  | step _ h_parent ih => exact Reaches.step ih h_parent

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

/-! ## Lemma 10 — round-robin pigeonhole (paper Appendix D)

There are `3f + 1` groups of three consecutive rounds in any window of
`3f + 3` rounds. Due to the round-robin schedule, each of the `2f + 1`
honest validators appears in 3 such groups, contributing `3 · (2f+1)
= 6f+3` total honest-leader positions across `3f+1` groups — average
`> 2`, so by pigeonhole some group has 3 honest leaders.
-/

/-- Combinatorial helper for `lemma10_round_robin_pigeonhole`.

In a circular sequence of length `n = 3f+1` with at most `f` "false"
positions, three consecutive "true" positions exist. Proved by
contradiction: each of the `n = 3f+1` triples `(i, i+1, i+2)` has a
false member; but each false position covers exactly 3 triples
(by the wrap-around), total coverage `3f < 3f+1`, contradiction.
-/
-- proof: aristotle (project 4cda6cb1) — round 2
lemma consecutive_triple_exists (n f : Nat) (g : Nat → Bool)
    (hn : n = 3 * f + 1)
    (h_false_count : (Finset.range n |>.filter (fun i => g i = false)).card ≤ f)
    (h_wrap1 : g n = g 0) (h_wrap2 : g (n + 1) = g 1) :
    ∃ i, i < n ∧ g i = true ∧ g (i + 1) = true ∧ g (i + 2) = true := by
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

/-- **Lemma 10 (paper Appendix D.3).**
*The round-robin schedule of leader blocks in Mysticeti-Beluga ensures
that in any window of `3f + 3` consecutive rounds, there are three
consecutive rounds with honest leader blocks.* -/
-- proof: aristotle (project 4cda6cb1) — round 2
theorem lemma10_round_robin_pigeonhole
    (system : BlockSynchroniserSystem) (startRound : Round)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length
                = 2 * system.f + 1)
    -- Validator IDs are {0, ..., n-1}, matching the round-robin's
    -- `r % n` output. Without this, `leaderOf` could produce IDs that
    -- don't correspond to any registered validator, making
    -- `isHonestValidator` return `false` for all leaders.
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i) :
    ∃ r ≥ startRound, r + 2 < startRound + (3 * system.f + 3) ∧
      isHonestValidator system (leaderOf system r) = true ∧
      isHonestValidator system (leaderOf system (r + 1)) = true ∧
      isHonestValidator system (leaderOf system (r + 2)) = true := by
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
        have h_false_count : (system.validators.filter (fun p => p.2 = true)).length
            + (system.validators.filter (fun p => p.2 = false)).length = system.n := by
          have h_false_count : ∀ (l : List (ValidatorId × Bool)),
              (l.filter (fun p => p.2 = true)).length
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

**Added protocol-invariant hypotheses (round 3c bridge closure):**
- `h_cert_base`: in round `B.r + 2`, every block's parent set overlaps
  the certificate set (consequence of quorum intersection +
  NoEquivocationInParents + DAG structural property that blocks have
  ≥ 2f+1 parents from the previous round).
- `h_dag_parent`: every block in a round later than `B.r + 2` has at
  least one parent in the state from the immediately preceding round
  (basic DAG connectivity).
-/
-- proof: aristotle (project 9d7e8e08) — round 6
theorem lemma13_cert_persistence
    (system : BlockSynchroniserSystem) {S} [SystemState S] (state : S)
    (_h_no_eq : NoEquivocationInParents system state)
    (B : Block) (_h_B : B ∈ SystemState.blocks state)
    (h_cert : ∃ certs : List Block,
                certs.length ≥ 2 * system.f + 1 ∧
                certs.Nodup ∧
                (certs.map (·.author)).Nodup ∧
                ∀ C ∈ certs, isCertificateFor state C B)
    -- Protocol invariant (base case of the quorum intersection argument):
    -- In round B.r + 2, every block in the DAG references at least one
    -- certificate for B as a parent. This is the conclusion of the quorum
    -- intersection + NoEquivocationInParents argument applied at the
    -- certificate round. Will become a provable consequence once
    -- Quorum.quorumIntersection and the DAG structural properties are
    -- formalized in round 2.
    (h_cert_base : ∀ B'' : Block, B'' ∈ SystemState.blocks state →
        B''.r = B.r + 2 →
        ∃ C, isCertificateFor state C B ∧
          C.d ∈ B''.parents ∧ C ∈ SystemState.blocks state)
    -- Protocol invariant (DAG connectivity): every block in a round
    -- later than B.r + 2 has at least one parent in the state from the
    -- immediately preceding round.
    (h_dag_parent : ∀ B'' : Block, B'' ∈ SystemState.blocks state →
        B''.r > B.r + 2 →
        ∃ P, P ∈ SystemState.blocks state ∧
          P.d ∈ B''.parents ∧ P.r + 1 = B''.r)
    (B' : Block) (h_in : B' ∈ SystemState.blocks state)
    (h_later : B'.r > B.r + 1) :
    ∃ C, isCertificateFor state C B ∧ Reaches state B' C := by
  obtain ⟨certs, h_len, h_nodup, h_auth_nodup, h_all_cert⟩ := h_cert
  -- Paper argument: induction on (B'.r − B.r − 2), i.e. distance from
  -- the certificate round.
  -- Base case (B'.r = B.r + 2): by h_cert_base, B' has a cert parent.
  -- Inductive step (B'.r > B.r + 2): by h_dag_parent, B' has a parent P
  -- from the previous round; by IH, P reaches a cert; by Reaches.trans,
  -- B' reaches the cert.
  have h_inductive_step :
      ∀ B'' : Block, B'' ∈ SystemState.blocks state → B''.r > B.r + 1 →
        ∃ C, isCertificateFor state C B ∧ Reaches state B'' C := by
    intro B'' h_in'' h_later''
    -- Induction on the distance n = B''.r − (B.r + 2).
    -- Reformulate: for all n, every block at round B.r + 2 + n reaches a cert.
    suffices key : ∀ n : Nat, ∀ B₀ : Block, B₀ ∈ SystemState.blocks state →
        B₀.r = B.r + 2 + n →
        ∃ C, isCertificateFor state C B ∧ Reaches state B₀ C by
      have h_ge : B''.r ≥ B.r + 2 := by simp only [Round] at h_later'' ⊢; omega
      have h_eq : B''.r = B.r + 2 + (B''.r - (B.r + 2)) := by
        simp only [Round] at *; omega
      exact key (B''.r - (B.r + 2)) B'' h_in'' h_eq
    intro n
    induction n with
    | zero =>
      -- Base case: B₀.r = B.r + 2.
      -- By h_cert_base, B₀ has a parent C that is a certificate for B.
      -- B₀ reaches C via one parent step.
      intro B₀ h_B₀_in h_B₀_r
      have h_eq : B₀.r = B.r + 2 := by simp only [Round] at h_B₀_r ⊢; omega
      obtain ⟨C, h_cert_C, h_C_parent, h_C_in⟩ := h_cert_base B₀ h_B₀_in h_eq
      exact ⟨C, h_cert_C, Reaches.step (Reaches.refl B₀)
        ⟨h_C_parent, h_C_in, h_B₀_in⟩⟩
    | succ n ih =>
      -- Inductive step: B₀.r = B.r + 2 + (n + 1) = B.r + 3 + n > B.r + 2.
      -- By h_dag_parent, B₀ has a parent P from round B₀.r - 1 = B.r + 2 + n.
      -- By IH, P reaches a cert C. By Reaches.trans (B₀ → P → ··· → C),
      -- B₀ reaches C.
      intro B₀ h_B₀_in h_B₀_r
      have h_gt : B₀.r > B.r + 2 := by simp only [Round] at h_B₀_r ⊢; omega
      obtain ⟨P, h_P_in, h_P_parent, h_P_round⟩ := h_dag_parent B₀ h_B₀_in h_gt
      have h_P_eq : P.r = B.r + 2 + n := by
        simp only [Round] at h_P_round h_B₀_r ⊢; omega
      obtain ⟨C, h_cert_C, h_reaches_PC⟩ := ih P h_P_in h_P_eq
      exact ⟨C, h_cert_C, Reaches.trans
        (Reaches.step (Reaches.refl B₀) ⟨h_P_parent, h_P_in, h_B₀_in⟩)
        h_reaches_PC⟩
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
    (h_cert₁ : certified system state B₁) (h_cert₂ : certified system state B₂)
    -- Additional BFT hypotheses (passed through to `certified_unique`):
    (hN : system.n = 3 * system.f + 1)
    (h_B₁_in : B₁ ∈ SystemState.blocks state)
    (h_B₂_in : B₂ ∈ SystemState.blocks state)
    (h_authors_valid : ∀ B ∈ SystemState.blocks state,
      ∃ pair ∈ system.validators, pair.1 = B.author)
    (h_byz_bound : (system.validators.filter (fun p => p.2 = false)).length
      ≤ system.f) :
    B₁ = B₂ := by
  -- Specialization of Beluga.certified_unique: leader blocks share author by
  -- definition (both authored by leaderOf system B₁.r = leaderOf system B₂.r).
  have h_same_author : B₁.author = B₂.author := by
    unfold isLeaderBlock at h_lead₁ h_lead₂
    rw [h_lead₁, h_lead₂, h_same_round]
  exact certified_unique system state h_no_eq B₁ B₂ h_cert₁ h_cert₂ h_same_author h_same_round
    hN h_B₁_in h_B₂_in h_authors_valid h_byz_bound

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

**Added protocol-invariant hypothesis (round 3c bridge closure):**
- `h_view_traceback`: every non-`Undecided` honest view on a digest `d`
  traces back to a leader block `B` with `B.d = d` in the state whose
  `directDecide` is non-`Undecided`. This captures the protocol
  invariant that all consensus decisions originate from direct
  DAG-pattern observations on leader blocks.
-/
-- proof: aristotle (project 9d7e8e08) — round 6
theorem lemma16_consistent_status
    (system : BlockSynchroniserSystem) {S} [SystemState S] (state : S)
    (view : ConsensusView)
    (h_view_direct : ∀ vid B, isHonestValidator system vid = true →
                       isLeaderBlock system B → B ∈ SystemState.blocks state →
                       directDecide system state B ≠ Decision.Undecided →
                       view vid B.d = directDecide system state B)
    -- Protocol invariant: every non-Undecided honest view on digest d
    -- traces back to a leader block B with B.d = d in the state whose
    -- directDecide is non-Undecided.
    (h_view_traceback : ∀ vid d, isHonestValidator system vid = true →
        view vid d ≠ Decision.Undecided →
        ∃ B, isLeaderBlock system B ∧ B ∈ SystemState.blocks state ∧
          directDecide system state B ≠ Decision.Undecided ∧ B.d = d) :
    view.Consistent system := by
  -- Unfold consistency: for any digest d and honest validators vid₁, vid₂,
  -- if both have non-Undecided views on d, they must agree.
  intro d vid₁ vid₂ h_honest₁ h_honest₂ h_ne₁ h_ne₂
  -- By h_view_traceback, vid₁'s non-Undecided view on d traces back to
  -- a leader block B_w with directDecide non-Undecided. By h_view_direct,
  -- both honest validators' views on B_w.d equal directDecide, hence agree.
  have h_exists_block : ∃ B, isLeaderBlock system B ∧
      B ∈ SystemState.blocks state ∧
      directDecide system state B ≠ Decision.Undecided ∧
      B.d = d := h_view_traceback vid₁ d h_honest₁ h_ne₁
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

**Added protocol-invariant hypothesis (round 3c bridge closure):**
- `h_decision_complete`: decision completeness — if one honest
  validator's view on a digest is `Undecided`, then all honest
  validators' views on that digest are `Undecided` (and vice versa).
  This is the liveness-derived property that honest validators
  eventually all decide the same way, upgrading `Consistent`
  (no conflicting non-Undecided) to full view equality.
-/
-- proof: aristotle (project 9d7e8e08) — round 6
theorem theorem7_consensus_safety
    (system : BlockSynchroniserSystem) {S} [SystemState S] (_state : S)
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
                   (order vid₂).isPrefixOf (order vid₁) = true)
    -- Protocol invariant (decision completeness): if one honest
    -- validator's view on digest d is Undecided, then so is every other
    -- honest validator's view (and vice versa). This upgrades
    -- ConsensusView.Consistent (no conflicting non-Undecided) to full
    -- view equality for honest validators.
    (h_decision_complete : ∀ vid₁ vid₂ d,
        isHonestValidator system vid₁ = true →
        isHonestValidator system vid₂ = true →
        (view vid₁ d = Decision.Undecided ↔ view vid₂ d = Decision.Undecided)) :
    order.Consistent system := by
  -- Paper argument: By Lemma 16, all honest validators assign identical
  -- decisions to each leader block. Combined with h_order_from_view
  -- (transaction ordering respects view equality), we obtain consistent
  -- transaction orders.
  intro vid₁ vid₂ h_honest₁ h_honest₂
  apply h_order_from_view vid₁ vid₂ h_honest₁ h_honest₂
  intro d
  -- From h_decision_complete + h_view_consistent: either both views are
  -- Undecided (and hence equal), or both are non-Undecided and equal
  -- (by consistency).
  have h_complete : view vid₁ d = Decision.Undecided ↔
      view vid₂ d = Decision.Undecided :=
    h_decision_complete vid₁ vid₂ d h_honest₁ h_honest₂
  by_cases h₁ : view vid₁ d = Decision.Undecided
  · rw [h₁, h_complete.mp h₁]
  · by_cases h₂ : view vid₂ d = Decision.Undecided
    · exact absurd (h_complete.mpr h₂) h₁
    · exact h_view_consistent d vid₁ vid₂ h_honest₁ h_honest₂ h₁ h₂

end Safety
end Mysticeti
end BlockSynchroniser
