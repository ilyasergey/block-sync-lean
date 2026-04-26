/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Mysticeti-Beluga safety bundle (paper Appendix D.3).
-/
import Mathlib.Tactic
import BlockSynchroniser.Block
import BlockSynchroniser.State
import BlockSynchroniser.System
import BlockSynchroniser.Causal
import BlockSynchroniser.Quorum
import BlockSynchroniser.Beluga.Patterns
import BlockSynchroniser.Beluga.AdmissionInvariant
import BlockSynchroniser.Mysticeti.SafetyInvariant
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

/-
In a list of ≥ f+1 registered validators, at least one is honest.
Follows from h_byz_bound: at most f validators are Byzantine, so a list
of > f registered validators contains at least one honest one.
-/
private lemma exists_honest_in_shared
    (system : BlockSynchroniserSystem)
    (shared : List ValidatorId)
    (h_shared_nodup : shared.Nodup)
    (h_shared_len : shared.length ≥ system.f + 1)
    (h_shared_valid : ∀ vid ∈ shared, ∃ pair ∈ system.validators, pair.1 = vid)
    (h_byz_bound : (system.validators.filter (fun p => p.2 = false)).length
      ≤ system.f) :
    ∃ v ∈ shared, isHonestValidator system v = true := by
  contrapose! h_byz_bound;
  refine' lt_of_lt_of_le h_shared_len _;
  have h_byzantine_count : List.toFinset (List.map (fun p => p.1) (List.filter (fun p => p.2 = false) system.validators)) ⊇ List.toFinset shared := by
    intro x hx; specialize h_byz_bound x; simp_all +decide [ isHonestValidator ] ;
    cases h_shared_valid x hx <;> simp_all +decide [ BlockSynchroniserSystem.isHonest ];
    cases h : List.find? ( fun x_1 => decide ( x_1.1 = x ) ) system.validators <;> simp_all +decide;
    · exact False.elim <| h x |>.2 ‹_› rfl;
    · grind;
  have := Finset.card_mono h_byzantine_count; simp_all +decide [ List.toFinset_card_of_nodup ] ;
  exact this.trans ( List.toFinset_card_le _ ) |> le_trans <| by simp +decide [ List.filter_eq ] ;

/--
**Lemma 13 (paper Appendix D.3).**

> *In Mysticeti-Beluga, if `2f + 1` round `r` blocks from distinct
> validators are certificates of a block `B`, then every block in
> any round `r' > r` must (directly or transitively) reference a
> certificate for `B` formed in round `r`.*

**Note on indexing.** The paper writes "round `r` blocks ... are
certificates of a block `B`", but a *certificate for `B`* is a
block in round `B.r + 1` (it references `B` as a parent). So the
paper's "round `r`" in this lemma refers to *the certificate's
round*, i.e., `r = B.r + 1`. Our Lean statement makes this explicit:
`B` is the block being certified, the certificates are at
`C.r = B.r + 1`, and we conclude for every `B'` with
`B'.r > B.r + 1` that `B'` `Reaches` some certificate for `B`.

The two phrasings are equivalent — the paper's `r' > r` becomes our
`B'.r > B.r + 1` after the index shift.

Paper proof sketch: consider round `B.r + 2`. Every block in this
round references `2f + 1` blocks from round `B.r + 1`. By quorum
intersection, any such set intersects the `2f + 1` certificates of
`B` in at least one honest validator. Since honest validators do
not equivocate, every round `B.r + 2` block must reference a
certificate for `B`. Induction on rounds propagates to all
`r' > B.r + 1`.
-/
-- proof: aristotle (project 9f17cf80) — admission-invariant round
theorem lemma13_cert_persistence
    (system : BlockSynchroniserSystem) {S} [SystemState S] (state : S)
    (_h_no_eq : NoEquivocationInParents system state)
    (h_admission : AdmissionWellFormed system state)
    -- Standard BFT side conditions (see "Notes on paper consistency"
    -- in `formalization.md` and findings F-2, F-3 in
    -- `docs/mechanization-findings.md`).
    (hN : system.n = 3 * system.f + 1)
    (h_authors_valid : ∀ B' ∈ SystemState.blocks state,
      ∃ pair ∈ system.validators, pair.1 = B'.author)
    (h_byz_bound : (system.validators.filter (fun p => p.2 = false)).length
      ≤ system.f)
    -- Honest validators produce at most one block per (author, round) pair.
    -- In a real protocol, this follows from digital signatures + honest behavior.
    (h_honest_unique : ∀ B₁ ∈ SystemState.blocks state, ∀ B₂ ∈ SystemState.blocks state,
      isHonestValidator system B₁.author = true →
      B₁.author = B₂.author → B₁.r = B₂.r → B₁ = B₂)
    (B : Block) (h_B : B ∈ SystemState.blocks state)
    (h_cert : ∃ certs : List Block,
                certs.length ≥ 2 * system.f + 1 ∧
                certs.Nodup ∧
                (certs.map (·.author)).Nodup ∧
                ∀ C ∈ certs, isCertificateFor state C B)
    (B' : Block) (h_in : B' ∈ SystemState.blocks state)
    (h_later : B'.r > B.r + 1) :
    ∃ C, isCertificateFor state C B ∧ Reaches state B' C := by
  -- The base case (round B.r + 2) is now derivable from
  -- `h_admission` + `h_cert` + `Quorum.quorumIntersection` +
  -- `h_no_eq` + `hN` (paper Appendix D's quorum-intersection step).
  -- The inductive step uses `h_admission` for the previous-round
  -- parent + IH + `Reaches.trans`.
  -- By induction on $d = B'.r - (B.r + 2)$, we can show that there exists a certificate for $B$ that $B'$ reaches.
  have h_ind : ∀ d ≥ 0, ∀ B' : Block, B' ∈ SystemState.blocks state → B'.r = B.r + 2 + d → ∃ C, isCertificateFor state C B ∧ Reaches state B' C := by
    intro d hd B' hB' hB'_r
    induction' d with d ih generalizing B';
    · obtain ⟨ certs, hcerts₁, hcerts₂, hcerts₃, hcerts₄ ⟩ := h_cert;
      obtain ⟨parents, hparents₁, hparents₂, hparents₃⟩ : ∃ parents : List Block, parents.length ≥ 2 * system.f + 1 ∧ (parents.map (·.author)).Nodup ∧ ∀ P ∈ parents, P ∈ SystemState.blocks state ∧ P.d ∈ B'.parents ∧ P.r + 1 = B'.r := by
        have := h_admission B' hB';
        grind;
      -- By quorum intersection, there exists a shared list of at least f+1 elements between parents and certs.
      obtain ⟨shared, hshared₁, hshared₂⟩ : ∃ shared : List ValidatorId, shared.Nodup ∧ shared.length ≥ system.f + 1 ∧ ∀ vid ∈ shared, vid ∈ parents.map (·.author) ∧ vid ∈ certs.map (·.author) := by
        apply Quorum.quorumIntersection system (parents.map (·.author)) (certs.map (·.author));
        · constructor;
          · assumption;
          · grind;
        · constructor;
          · assumption;
          · grind +locals;
        · exact hN;
      obtain ⟨v, hv⟩ : ∃ v ∈ shared, isHonestValidator system v = true := by
        apply exists_honest_in_shared;
        · assumption;
        · linarith;
        · grind;
        · exact h_byz_bound;
      obtain ⟨P, hP⟩ : ∃ P ∈ parents, P.author = v := by
        simpa using hshared₂.2 v hv.1 |>.1
      obtain ⟨C, hC⟩ : ∃ C ∈ certs, C.author = v := by
        simpa using hshared₂.2 v hv.1 |>.2;
      have hP_eq_C : P = C := by
        grind +locals;
      use C;
      exact ⟨ hcerts₄ C hC.1, Reaches.step ( Reaches.refl _ ) ⟨ by aesop, by aesop, by aesop ⟩ ⟩;
    · -- By the admission invariant, B' has parents with ≥ 2f+1 entries, each P at round B'.r - 1.
      obtain ⟨parents, h_parents⟩ : ∃ parents : List Block, parents.length ≥ 2 * system.f + 1 ∧ (parents.map (·.author)).Nodup ∧ ∀ P ∈ parents, P ∈ SystemState.blocks state ∧ P.d ∈ B'.parents ∧ P.r = B'.r - 1 := by
        have := h_admission B' hB' (by
        grind);
        exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.1, fun P hP => ⟨ this.choose_spec.2.2 P hP |>.1, this.choose_spec.2.2 P hP |>.2.1, eq_tsub_of_add_eq <| this.choose_spec.2.2 P hP |>.2.2 ⟩ ⟩;
      obtain ⟨P, hP⟩ : ∃ P ∈ parents, ∃ C, isCertificateFor state C B ∧ Reaches state P C := by
        rcases parents <;> aesop;
      obtain ⟨ C, hC₁, hC₂ ⟩ := hP.2;
      exact ⟨ C, hC₁, Reaches.step ( Reaches.refl _ ) ⟨ h_parents.2.2 P hP.1 |>.2.1, h_parents.2.2 P hP.1 |>.1, hB' ⟩ |> Reaches.trans <| hC₂ ⟩;
  exact h_ind ( B'.r - ( B.r + 2 ) ) ( Nat.zero_le _ ) B' h_in ( by rw [ add_tsub_cancel_of_le h_later ] )

/--
**Lemma 14 (paper Appendix D.3).**

> *In Mysticeti-Beluga, if an honest validator directly commits
> `B_r^L`, then no honest validator (directly or indirectly)
> decides to skip `B_r^L`.*

Paper proof sketch (two cases):
* *Direct skip.* A direct skip occurs only if at least `2f + 1`
  blocks in round `r + 1` do not reference `B_r^L`. But if `B_r^L`
  is committed, then by the decision rule, at least `2f + 1` round
  `r + 1` blocks reference it. The two `2f + 1`-quorums intersect
  in at least one honest validator, who would have to equivocate —
  contradiction.
* *Indirect skip.* An indirect skip occurs through a later leader
  `B_{r'}^L` with `r' > r + 2` whose causal history does not
  reference any certificate for `B_r^L`. But `B_r^L` is directly
  committed, so it has `2f + 1` certificates; by Lemma 13, every
  block in rounds `> r + 1` references one of them — contradiction.

In our Lean statement the "no skip" claim is reduced to
`view vid B.d ≠ Decision.ToSkip` for every honest `vid`, given
`directDecide system state B = Decision.ToCommit` and the protocol
fact that honest views agree with `directDecide` on this digest.
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

> *In Mysticeti-Beluga, at most one leader block can be certified
> for any round `r`.*

This is a *specialization* of
[`Beluga.certified_unique`](../Beluga/Patterns.lean): restrict to
leader blocks (where `author = leaderOf system r`); uniqueness then
follows from the existing quorum-intersection chain.

Paper proof sketch:

> *Suppose two distinct leader blocks `B_{r,L_1}` and `B_{r,L_2}`
> both obtain `2f + 1` references from round `r + 1`. By quorum
> intersection, at least one honest validator must belong to both
> quorums, and thus would have referenced both blocks in round `r`.
> This contradicts the protocol rule that a validator references
> at most one block per proposer per round.*

The paper notes immediately after L15:

> **Corollary 1.** *No two honest validators commit distinct leader
> blocks in the same round.*

(Used in the base case of L16's backward induction below.)
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

> *In Mysticeti-Beluga, all honest validators decide a consistent
> status for each round leader block.*

Paper proof (verbatim):

> *Consider two honest validators `v_i` and `v_j`, and let `n` be
> the highest round in which `v_i` commits a leader block. We prove
> by backward induction that for every round `x ≤ n`, both
> validators assign the same status to `B_x^L`.*
>
> *Base case (`x = n`).* Validator `v_i` commits `B_n^L`. By Lemma
> 14, `v_j` cannot skip it and must also commit it. By Corollary 1
> (no two honest validators commit distinct leader blocks in the
> same round), both commit the same block.
>
> *Inductive step.* Assume the statement holds for all rounds in
> `(k, n]`. Consider round `k`. If either validator directly commits
> or directly skips `B_k^L`, the other must make the same decision
> by Lemma 11 and Lemma 14. Otherwise, both decisions are indirect
> and derived from a later committed leader. Let `k_i` and `k_j` be
> the rounds of the first such commits for `v_i` and `v_j`,
> respectively. By the induction hypothesis, `k_i = k_j`, and both
> validators commit the same leader block. Since indirect decisions
> depend only on the causal history of that block, both validators
> derive the same decision for `B_k^L`.

**Mechanization note.** Our `view.Consistent` only requires that
two non-`Undecided` honest views agree (the safety claim), not the
fuller "decide on the same set of leader blocks" claim used in the
paper's induction. The two are bridged by **decision completeness**
(see `h_decision_complete` on `theorem7_consensus_safety` below) —
a liveness consequence the paper invokes silently. This is finding
**F-7(a)** in `docs/mechanization-findings.md`.

**Added protocol-invariant hypothesis (round 3c bridge closure):**
- `h_view_traceback` — every non-`Undecided` honest view on a digest
  `d` traces back to a leader block `B` with `B.d = d` in the state
  whose `directDecide` is non-`Undecided`. This captures the protocol
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
**Theorem 7 (paper Appendix D.3) — Consensus safety.**

> *In Mysticeti-Beluga, all honest validators order transactions
> consistently.*

Paper proof (verbatim):

> *By Lemma 16, all honest validators decide a consistent status for
> each round leader block, meaning that all honest validators
> decide identical to-commit leader blocks. According to the
> consensus logic employed by Mysticeti-Beluga, all honest
> validators will order to-commit leader blocks and their causal
> history block consistently. Therefore, for transactions included
> in the ordered blocks, all honest validators order them
> consistently.*

**Mechanization notes** (findings F-7(a), F-7(b) in
`docs/mechanization-findings.md`):

- *F-7(a)* — the paper's "decide identical leader blocks" overstates
  Lemma 16, which only gives *consistency* (no two honest validators
  decide non-`Undecided` differently) — not full *equality* of
  decided sets, which is a liveness property. We surface
  `h_decision_complete` as an explicit hypothesis to bridge the gap.

- *F-7(b)* — "transaction ordering respects view equality" is silently
  relied on. We surface this as `h_order_from_view`. For the
  `belugaTrace` instantiation a concrete realization is provided in
  `Beluga/Order.lean` (`belugaTransactionOrder` +
  `accepted_implies_in_belugaTransactionOrder`).

**Added protocol-invariant hypothesis (round 3c bridge closure):**
- `h_decision_complete` — decision completeness: if one honest
  validator's view on a digest is `Undecided`, then all honest
  validators' views on that digest are `Undecided` (and vice versa).
  This is the liveness-derived property that honest validators
  eventually all decide the same way, upgrading `Consistent`
  (no conflicting non-`Undecided`) to full view equality.
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

/-! ## belugaTrace-specialised wrappers

For the executable `belugaTrace` instantiation, the four
protocol-invariant hypotheses on L13 / L15
(`AdmissionWellFormed`, `NoEquivocationInParents`, the
honest-author uniqueness assumption, the authors-are-registered side
condition) are not assumptions: they are bundled in
`Mysticeti.MysticetiSafetyInv` and proved by
`belugaTrace_satisfies_mysticetiSafetyInv` (modulo the
`authorsValid` conjunct, queued for delegation).

These wrappers consume the bundle and re-state L13 / L15 against
`belugaTrace`, leaving only the genuine BFT side conditions (`hN`,
`h_byz_bound`, `hids`) — paper assumptions that cannot be derived
from the executable trace. -/

/-- **Lemma 13 (paper Appendix D.3) for the Beluga trace.**

belugaTrace specialisation of `lemma13_cert_persistence`. The four
protocol-invariant hypotheses (`h_no_eq`, `h_admission`,
`h_authors_valid`, `h_honest_unique`) are discharged from
[`belugaTrace_satisfies_mysticetiSafetyInv`](SafetyInvariant.lean). -/
theorem lemma13_cert_persistence_belugaTrace
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (hN : system.n = 3 * system.f + 1)
    (h_byz_bound : (system.validators.filter (fun p => p.2 = false)).length
      ≤ system.f)
    (k : Nat)
    (B : Block) (h_B : B ∈ (Beluga.belugaTrace system k).blocks)
    (h_cert : ∃ certs : List Block,
                certs.length ≥ 2 * system.f + 1 ∧
                certs.Nodup ∧
                (certs.map (·.author)).Nodup ∧
                ∀ C ∈ certs, isCertificateFor (Beluga.belugaTrace system k) C B)
    (B' : Block) (h_in : B' ∈ (Beluga.belugaTrace system k).blocks)
    (h_later : B'.r > B.r + 1) :
    ∃ C, isCertificateFor (Beluga.belugaTrace system k) C B ∧
         Reaches (Beluga.belugaTrace system k) B' C := by
  have h_inv := belugaTrace_satisfies_mysticetiSafetyInv system hids k
  exact lemma13_cert_persistence system (Beluga.belugaTrace system k)
    h_inv.noEquivocation h_inv.admission hN h_inv.authorsValid h_byz_bound
    (fun B₁ hB₁ B₂ hB₂ _ => h_inv.uniqueByAuthorRound B₁ hB₁ B₂ hB₂)
    B h_B h_cert B' h_in h_later

/-- **Lemma 15 (paper Appendix D.3) for the Beluga trace.**

belugaTrace specialisation of `lemma15_unique_cert`. The four
protocol-invariant hypotheses (`h_no_eq`, `h_authors_valid`,
`h_byz_bound` is kept since it is a system-wide BFT side condition)
are discharged from
[`belugaTrace_satisfies_mysticetiSafetyInv`](SafetyInvariant.lean). -/
theorem lemma15_unique_cert_belugaTrace
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (hN : system.n = 3 * system.f + 1)
    (h_byz_bound : (system.validators.filter (fun p => p.2 = false)).length
      ≤ system.f)
    (k : Nat)
    (B₁ B₂ : Block)
    (h_lead₁ : isLeaderBlock system B₁) (h_lead₂ : isLeaderBlock system B₂)
    (h_same_round : B₁.r = B₂.r)
    (h_cert₁ : Beluga.certified system (Beluga.belugaTrace system k) B₁)
    (h_cert₂ : Beluga.certified system (Beluga.belugaTrace system k) B₂)
    (h_B₁_in : B₁ ∈ (Beluga.belugaTrace system k).blocks)
    (h_B₂_in : B₂ ∈ (Beluga.belugaTrace system k).blocks) :
    B₁ = B₂ := by
  have h_inv := belugaTrace_satisfies_mysticetiSafetyInv system hids k
  exact lemma15_unique_cert system (Beluga.belugaTrace system k)
    h_inv.noEquivocation B₁ B₂ h_lead₁ h_lead₂ h_same_round
    h_cert₁ h_cert₂ hN h_B₁_in h_B₂_in h_inv.authorsValid h_byz_bound

end Safety
end Mysticeti
end BlockSynchroniser
