/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Block patterns (paper §4.4).
-/
import Mathlib.Tactic
import BlockSynchroniser.Block
import BlockSynchroniser.System
import BlockSynchroniser.State
import BlockSynchroniser.Quorum

set_option linter.unusedSimpArgs false

namespace BlockSynchroniser
namespace Beluga

/-- The distinct authors of blocks in `state` that reference `B` *as a parent*
(strong link). Used by both pattern definitions below. -/
def strongReferencerAuthors {S} [SystemState S] (state : S) (B : Block) : List ValidatorId :=
  ((SystemState.blocks state).filter (fun B' => B.d ∈ B'.parents)).map (·.author)
    |>.eraseDups

/--
**Availability pattern (paper §4.4).**

`B` forms an availability pattern if it is referenced by more than `f` distinct
validators' blocks. Per the paper, "referenced" includes both strong links
(parents) and weak links (weaklinks). For now we conservatively count strong
links only — every weak-link-included reference is at least as inclusive, so
this lower-bounds the paper's notion.

A block forming an availability pattern is called *available*: at least one
honest validator can attest to its causal availability.
-/
def availabilityPattern (system : BlockSynchroniserSystem) {S} [SystemState S]
    (state : S) (B : Block) : Prop :=
  (strongReferencerAuthors state B).length > system.f

/--
**Certificate pattern (paper §4.4).**

`B` forms a certificate pattern if it is referenced *as parents* by more than
`2f` distinct validators' blocks. A block forming a certificate pattern is
called *certified*; certificates underlie consensus uniqueness.
-/
def certificatePattern (system : BlockSynchroniserSystem) {S} [SystemState S]
    (state : S) (B : Block) : Prop :=
  (strongReferencerAuthors state B).length > 2 * system.f

/-- An *available* block (paper §4.4 — block forming an availability pattern). -/
abbrev available := availabilityPattern

/-- A *certified* block (paper §4.4 — block forming a certificate pattern). -/
abbrev certified := certificatePattern

/--
Honest validators don't reference equivocating parents — *cross-block*
version.

Captures the safety property that, in any state induced by a correct
execution, no two honest validators (whether the same one or two distinct
ones) ever reference conflicting blocks for the same `(author, round)`
pair. In Beluga this is enforced by the admission-control module; we
state it abstractly here as a hypothesis on the state.

The within-block specialization (`B₁ = B₂`) is the simpler form
"honest validators don't include two parents from the same proposer
round in their own block." The cross-block form additionally rules out
"honest validators reference different round-`r` blocks of the same
author across two of their own blocks" — needed for `certified_unique`'s
proof where the shared honest validator may have referenced `B₁` and
`B₂` from two different blocks of theirs.
-/
def NoEquivocationInParents (system : BlockSynchroniserSystem) {S} [SystemState S]
    (state : S) : Prop :=
  ∀ B₁ B₂ parent₁ parent₂,
    B₁ ∈ SystemState.blocks state →
    B₂ ∈ SystemState.blocks state →
    isHonestValidator system B₁.author = true →
    isHonestValidator system B₂.author = true →
    parent₁ ∈ SystemState.blocks state →
    parent₂ ∈ SystemState.blocks state →
    parent₁.d ∈ B₁.parents →
    parent₂.d ∈ B₂.parents →
    parent₁.author = parent₂.author →
    parent₁.r = parent₂.r →
    parent₁ = parent₂

/-! ## Helper lemmas for `certified_unique` -/

/-
`strongReferencerAuthors` produces duplicate-free lists (by `eraseDups`).
-/
lemma strongReferencerAuthors_nodup {S} [SystemState S] (state : S) (B : Block) :
    (strongReferencerAuthors state B).Nodup := by
  -- By definition of `List.eraseDupsBy.loop`, the list is nodup.
  have h_loop_nodup : ∀ (l : List ValidatorId) (acc : List ValidatorId), List.Nodup acc → List.Nodup (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc) := by
    intros l acc hacc; induction' l with hd tl ih generalizing acc <;> simp_all +decide [ List.eraseDupsBy.loop ] ;
    cases h : acc.any fun x2 => hd == x2 <;> simp_all +decide;
    grind;
  exact h_loop_nodup _ _ ( by simp +decide )

/-
Membership in `strongReferencerAuthors` witnesses a referencing block.
-/
lemma strongReferencerAuthors_mem {S} [SystemState S] (state : S) (B : Block) (vid : ValidatorId) :
    vid ∈ strongReferencerAuthors state B →
    ∃ C ∈ SystemState.blocks state, C.author = vid ∧ B.d ∈ C.parents := by
  intro h;
  unfold strongReferencerAuthors at h;
  have h_eraseDups : ∀ {l : List ValidatorId}, vid ∈ List.eraseDups l → vid ∈ l := by
    intros l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ List.eraseDups_append ] ;
    grind +suggestions;
  grind

/-
Elements of `strongReferencerAuthors` are registered validator IDs
    (assuming all block authors in the state are registered).
-/
lemma strongReferencerAuthors_are_validators {S} [SystemState S]
    (system : BlockSynchroniserSystem) (state : S) (B : Block)
    (h_valid : ∀ B ∈ SystemState.blocks state, ∃ pair ∈ system.validators, pair.1 = B.author) :
    ∀ vid ∈ strongReferencerAuthors state B, ∃ pair ∈ system.validators, pair.1 = vid := by
  intros vid hvid
  obtain ⟨C, hC⟩ : ∃ C ∈ SystemState.blocks state, C.author = vid ∧ B.d ∈ C.parents := by
    exact strongReferencerAuthors_mem state B vid hvid
  simpa only [hC.2.1] using h_valid C hC.1

/-
**Uniqueness of certified blocks per `(author, round)` (paper §4.4).**

> *"the certificate pattern implies uniqueness: for any validator and round,
> at most one block can become certified"* — paper §4.4 (page 9).

Stated as an informal consequence in §4.4 (no lemma number); we formalize it
here. Specializing `B₁.author = B₂.author = leader(r)` gives Appendix D
**Lemma 15** ("at most one leader block can be certified for any round r"),
which is the load-bearing form for the Mysticeti-Beluga safety theorem.

The following additional hypotheses beyond the original statement were
required for the formalization (they are standard BFT assumptions implicit
in the paper's reasoning):
- `hN`: the system has exactly `3f+1` validators (needed for quorum intersection)
- `h_B₁_in`, `h_B₂_in`: both certified blocks are in the state (needed for `NoEquivocationInParents`)
- `h_authors_valid`: all block authors are registered validators (bounds the universe)
- `h_byz_bound`: at most `f` validators are Byzantine (needed to find an honest validator in the intersection)
-/
theorem certified_unique
    {S} [SystemState S] (system : BlockSynchroniserSystem) (state : S)
    (h_no_equivocation : NoEquivocationInParents system state)
    (B₁ B₂ : Block)
    (h_cert₁ : certified system state B₁)
    (h_cert₂ : certified system state B₂)
    (h_same_author : B₁.author = B₂.author)
    (h_same_round  : B₁.r      = B₂.r)
    -- Additional BFT hypotheses (implicit in the paper):
    (hN : system.n = 3 * system.f + 1)
    (h_B₁_in : B₁ ∈ SystemState.blocks state)
    (h_B₂_in : B₂ ∈ SystemState.blocks state)
    (h_authors_valid : ∀ B ∈ SystemState.blocks state,
      ∃ pair ∈ system.validators, pair.1 = B.author)
    (h_byz_bound : (system.validators.filter (fun p => p.2 = false)).length
      ≤ system.f) :
    B₁ = B₂ := by
  -- Apply the quorum intersection lemma to get a shared list with length ≥ f+1 and ∀ vid ∈ shared, vid ∈ S₁ ∧ vid ∈ S₂.
  obtain ⟨shared, h_shared_nodup, h_shared_length, h_shared_mem⟩ : ∃ shared : List ValidatorId, shared.Nodup ∧ shared.length ≥ system.f + 1 ∧ ∀ vid ∈ shared, vid ∈ strongReferencerAuthors state B₁ ∧ vid ∈ strongReferencerAuthors state B₂ := by
    apply Quorum.quorumIntersection system (strongReferencerAuthors state B₁) (strongReferencerAuthors state B₂);
    · constructor
      · exact strongReferencerAuthors_nodup state B₁
      · exact ⟨h_cert₁, strongReferencerAuthors_are_validators system state B₁ h_authors_valid⟩
    · exact ⟨ strongReferencerAuthors_nodup state B₂, h_cert₂, fun vid h => strongReferencerAuthors_are_validators system state B₂ h_authors_valid vid h ⟩;
    · exact hN;
  obtain ⟨h, hh⟩ : ∃ h ∈ shared, isHonestValidator system h = true := by
    contrapose! h_byz_bound;
    have h_byz_list : List.toFinset (List.filter (fun p => p.2 = false) system.validators |>.map (·.1)) ⊇ List.toFinset shared := by
      intro x hx; specialize h_shared_mem x; specialize h_byz_bound x; simp_all +decide [ Finset.subset_iff ] ;
      obtain ⟨ C₁, hC₁, hC₁' ⟩ := strongReferencerAuthors_mem state B₁ x h_shared_mem.1; specialize h_authors_valid C₁ hC₁; simp_all +decide [ isHonestValidator ] ;
      cases h : system.validators.find? ( fun p => p.1 = x ) <;> simp_all +decide [ BlockSynchroniserSystem.isHonest ];
      · grind +splitIndPred;
      · grind;
    have := Finset.card_le_card h_byz_list; simp_all +decide [ List.toFinset_card_of_nodup ] ;
    exact h_shared_length.trans_le ( this.trans ( List.toFinset_card_le _ ) |> le_trans <| by simp +decide [ List.toFinset_card_le ] );
  have := strongReferencerAuthors_mem state B₁ h ( h_shared_mem h hh.1 |>.1 ) ; have := strongReferencerAuthors_mem state B₂ h ( h_shared_mem h hh.1 |>.2 ) ; aesop;

end Beluga
end BlockSynchroniser