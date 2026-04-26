/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Admission well-formedness as a trace invariant of `belugaTrace`.
-/
import Mathlib.Tactic
import BlockSynchroniser.Block
import BlockSynchroniser.System
import BlockSynchroniser.State
import BlockSynchroniser.Beluga.Protocol

set_option maxHeartbeats 800000

-- proof: aristotle (project 9f17cf80) — admission-invariant round
-- The compound `TraceInv` carrier, all per-action preservation
-- lemmas, and the trace-induction proof of
-- `belugaTrace_admissionWellFormed` were introduced by this round.

namespace BlockSynchroniser
namespace Beluga

/-- A state's blocks satisfy *admission well-formedness* if every block
at round `> 0` has at least `2f+1` distinct-author parents from the
immediately preceding round, all themselves in the state.

This is the structural DAG invariant the paper treats as obvious in
the proofs of Mysticeti-Beluga safety (Appendix D.3). It is a
consequence of the protocol's parent-selection rule + Beluga's
admission control — **not** an adversary constraint.
-/
def AdmissionWellFormed (system : BlockSynchroniserSystem) {S} [SystemState S]
    (state : S) : Prop :=
  ∀ B ∈ SystemState.blocks state, B.r > 0 →
    ∃ parents : List Block,
      parents.length ≥ 2 * system.f + 1 ∧
      (parents.map (·.author)).Nodup ∧
      ∀ P ∈ parents,
        P ∈ SystemState.blocks state ∧
        P.d ∈ B.parents ∧
        P.r + 1 = B.r

/-! ## Compound trace invariant -/

private def TraceInv (system : BlockSynchroniserSystem) (s : BelugaState) : Prop :=
  AdmissionWellFormed system s ∧
  (∀ vid B r, (ValidatorOperation.block_propose vid B r) ∈ s.emittedOperations →
    B ∈ s.blocks ∧ B.author = vid ∧ B.r = r) ∧
  (s.validators.map Prod.fst = system.validators.map Prod.fst) ∧
  (∀ p ∈ s.validators, p.2.currentRound > 0 →
    allProposedFor system s (p.2.currentRound - 1) = true)

/-! ## Helper lemmas -/

private lemma traceInv_init (system : BlockSynchroniserSystem) :
    TraceInv system (BelugaState.init system) := by
  constructor
  · intro B hB
    cases hB
  · unfold BelugaState.init; aesop

private lemma hasProposedFor_append (s : BelugaState) (vid : ValidatorId) (r : Round)
    (ops : List ValidatorOperation)
    (h : hasProposedFor s vid r = true) :
    hasProposedFor { s with emittedOperations := s.emittedOperations ++ ops } vid r = true := by
  simp [hasProposedFor] at h ⊢
  simp [List.any_append, h]

private lemma allProposedFor_append (system : BlockSynchroniserSystem)
    (s : BelugaState) (r : Round) (ops : List ValidatorOperation)
    (h : allProposedFor system s r = true) :
    allProposedFor system { s with emittedOperations := s.emittedOperations ++ ops } r = true := by
  unfold allProposedFor at *
  grind +suggestions

private lemma allProposedFor_of_same_ops (system : BlockSynchroniserSystem)
    (s s' : BelugaState) (r : Round)
    (h_ops : s'.emittedOperations = s.emittedOperations)
    (h : allProposedFor system s r = true) :
    allProposedFor system s' r = true := by
  unfold allProposedFor at *
  unfold hasProposedFor at *
  grind

private lemma updateValidator_map_fst (s : BelugaState) (vid : ValidatorId)
    (f : BelugaValidator → BelugaValidator) :
    (updateValidator s vid f).validators.map Prod.fst = s.validators.map Prod.fst := by
  unfold updateValidator; aesop

private lemma admission_of_same_blocks (system : BlockSynchroniserSystem)
    (s s' : BelugaState)
    (h_blocks : s'.blocks = s.blocks)
    (h_adm : AdmissionWellFormed system s) :
    AdmissionWellFormed system s' := by
  unfold AdmissionWellFormed at *
  unfold instSystemStateBelugaState at *; aesop

private lemma admission_of_cons_blocks (system : BlockSynchroniserSystem)
    (s : BelugaState) (newB : Block)
    (h_adm : AdmissionWellFormed system s) :
    ∀ B ∈ s.blocks, B.r > 0 →
      ∃ parents : List Block,
        parents.length ≥ 2 * system.f + 1 ∧
        (parents.map (·.author)).Nodup ∧
        ∀ P ∈ parents,
          P ∈ (newB :: s.blocks : List Block) ∧
          P.d ∈ B.parents ∧
          P.r + 1 = B.r := by
  exact fun B hB hB' => by
    rcases h_adm B hB hB' with ⟨parents, h1, h2, h3⟩
    exact ⟨parents, h1, h2, fun P hP =>
      ⟨List.mem_cons_of_mem _ (h3 P hP).1, (h3 P hP).2.1, (h3 P hP).2.2⟩⟩

private lemma allProposedFor_gives_blocks
    (system : BlockSynchroniserSystem) (s : BelugaState) (r : Round)
    (h_all : allProposedFor system s r = true)
    (h_ops : ∀ vid B r, (ValidatorOperation.block_propose vid B r) ∈ s.emittedOperations →
      B ∈ s.blocks ∧ B.author = vid ∧ B.r = r) :
    ∀ p ∈ system.validators, ∃ B ∈ s.blocks, B.author = p.1 ∧ B.r = r := by
  unfold allProposedFor at h_all
  unfold hasProposedFor at h_all
  grind

/-! ## Per-action TraceInv preservation -/

/-
TraceInv preserved by doPropose.
-/
private lemma traceInv_of_doPropose (system : BlockSynchroniserSystem)
    (s : BelugaState) (vid : ValidatorId) (bv : BelugaValidator)
    (h : TraceInv system s)
    (hmem : (vid, bv) ∈ s.validators) :
    TraceInv system (doPropose system s vid bv.currentRound) := by
  constructor;
  · obtain ⟨h_adm, h_ops, h_ids, h_adv⟩ := h;
    intro B hB hB';
    by_cases hB'' : B = ⟨ bv.currentRound, vid, digest system bv.currentRound vid, if bv.currentRound = 0 then [] else ( s.blocks.filter ( fun B => B.r == bv.currentRound - 1 ) ).map ( ·.d ), [] ⟩;
    · by_cases h : bv.currentRound > 0 <;> simp_all +decide;
      have := h_adv vid bv hmem h;
      obtain ⟨parents, h_parents⟩ : ∃ parents : List Block, parents.length ≥ 2 * system.f + 1 ∧ (parents.map (·.author)).Nodup ∧ ∀ P ∈ parents, P ∈ s.blocks ∧ P.r = bv.currentRound - 1 := by
        have := allProposedFor_gives_blocks system s (bv.currentRound - 1) this;
        have h_parents : ∃ parents : List ValidatorId, parents.length ≥ 2 * system.f + 1 ∧ (parents.map (fun x => x)).Nodup ∧ ∀ p ∈ parents, ∃ B ∈ s.blocks, B.author = p ∧ B.r = bv.currentRound - 1 := by
          have h_parents : ∃ parents : List ValidatorId, parents.length ≥ 2 * system.f + 1 ∧ (parents.map (fun x => x)).Nodup ∧ ∀ p ∈ parents, p ∈ system.validators.map Prod.fst := by
            have h_parents : (system.validators.map Prod.fst).length ≥ 2 * system.f + 1 := by
              have := system.honestMajority; have := system.validatorCountCorrect; norm_num at *; linarith;
            have h_parents : (system.validators.map Prod.fst).Nodup :=
              system.validatorsNodup;
            exact ⟨ _, by assumption, by simpa using h_parents, fun p hp => by simpa using hp ⟩;
          grind;
        obtain ⟨ parents, hparents₁, hparents₂, hparents₃ ⟩ := h_parents;
        choose! f hf₁ hf₂ using hparents₃;
        use parents.pmap (fun p hp => f p hp) (by
        exact fun x hx => hx)
        generalize_proofs at *;
        grind;
      use parents;
      simp_all +decide [ doPropose ];
      exact fun P hP => ⟨ List.mem_cons_of_mem _ ( h_parents.2.2 P hP |>.1 ), ⟨ ne_of_gt h, P, h_parents.2.2 P hP, rfl ⟩, Nat.succ_pred_eq_of_pos h ⟩;
    · convert admission_of_cons_blocks system s _ h_adm B _ hB' using 1;
      exact List.mem_of_ne_of_mem hB'' hB;
  · unfold doPropose;
    constructor;
    · grind +locals;
    · exact ⟨ h.2.2.1, fun p hp hp' => allProposedFor_append _ _ _ _ ( h.2.2.2 p hp hp' ) ⟩

/-
TraceInv preserved by doAccept.
-/
private lemma traceInv_of_doAccept (system : BlockSynchroniserSystem)
    (s : BelugaState) (vid : ValidatorId) (B : Block)
    (h : TraceInv system s) :
    TraceInv system (doAccept s vid B) := by
  constructor;
  · exact admission_of_same_blocks system s _ rfl h.1;
  · constructor;
    · intro vid_1 B_1 r h_propose
      have h_propose_in_s : ValidatorOperation.block_propose vid_1 B_1 r ∈ s.emittedOperations := by
        unfold doAccept at h_propose;
        unfold updateValidator at h_propose; aesop;
      have := h.2.1 vid_1 B_1 r h_propose_in_s; aesop;
    · constructor;
      · convert h.2.2.1 using 1;
        exact updateValidator_map_fst _ _ _;
      · unfold doAccept;
        intro p hp hp'; simp_all +decide [ updateValidator ] ;
        convert allProposedFor_append system s ( p.2.currentRound - 1 ) [ ValidatorOperation.block_accept vid B.d ] _ using 1;
        grind +locals

/-
TraceInv preserved by doStore.
-/
private lemma traceInv_of_doStore (system : BlockSynchroniserSystem)
    (s : BelugaState) (vid : ValidatorId) (B : Block)
    (h : TraceInv system s) :
    TraceInv system (doStore s vid B) := by
  constructor;
  · convert admission_of_same_blocks system s ( doStore s vid B ) _ h.1 using 1;
    simp [doStore, updateValidator];
  · constructor <;> simp_all +decide [ doStore ];
    · intro vid B r hr; have := h.2.1 vid B r; simp_all +decide [ updateValidator ] ;
    · constructor;
      · convert h.2.2.1 using 1;
        exact updateValidator_map_fst _ _ _;
      · intro a b hb hb'; rcases h with ⟨ h₁, h₂, h₃, h₄ ⟩ ; simp_all +decide [ updateValidator ] ;
        convert allProposedFor_append system s ( b.currentRound - 1 ) [ ValidatorOperation.block_store vid B ] _ using 1;
        grind +locals

/-
TraceInv preserved by doAdvance (given allProposedFor gate).
-/
private lemma traceInv_of_doAdvance (system : BlockSynchroniserSystem)
    (s : BelugaState) (vid : ValidatorId) (bv : BelugaValidator)
    (h : TraceInv system s)
    (hmem : (vid, bv) ∈ s.validators)
    (h_all : allProposedFor system s bv.currentRound = true) :
    TraceInv system (doAdvance s vid) := by
  refine' ⟨ _, _, _, _ ⟩;
  · exact admission_of_same_blocks system _ _ rfl h.1;
  · exact h.2.1;
  · exact h.2.2.1 ▸ updateValidator_map_fst s vid _;
  · intro p hp hpos
    simp [doAdvance] at hp;
    by_cases h : p.1 = vid <;> simp_all +decide [ updateValidator ];
    · have h_val_eq : List.Nodup (s.validators.map Prod.fst) := by
        have h_val_eq : List.Nodup (system.validators.map Prod.fst) :=
          system.validatorsNodup
        have := ‹TraceInv system s›.2.2.1; aesop;
      rw [ List.nodup_iff_injective_get ] at h_val_eq;
      obtain ⟨ a, b, hab, rfl ⟩ := hp;
      obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hab; obtain ⟨ j, hj ⟩ := List.mem_iff_get.mp hmem; simp_all +decide [ h_val_eq.eq_iff ] ;
      have := @h_val_eq ⟨ i, by simp ⟩ ⟨ j, by simp ⟩ ; aesop;
    · obtain ⟨ a, b, h₁, rfl ⟩ := hp; simp_all +decide [ doAdvance ] ;
      exact allProposedFor_of_same_ops system _ _ _ rfl ( by have := ‹TraceInv system s›.2.2.2 ( a, b ) h₁; aesop )

/-
TraceInv is preserved by step.
-/
private lemma traceInv_step (system : BlockSynchroniserSystem)
    (s : BelugaState) (h : TraceInv system s) :
    TraceInv system (step system s) := by
  unfold step;
  cases h' : List.findSome? ( fun x => tryActFor system s x.1 x.2 ) s.validators <;> simp_all +decide;
  rw [ List.findSome?_eq_some_iff ] at h';
  obtain ⟨ l₁, a, l₂, h₁, h₂, h₃ ⟩ := h';
  unfold tryActFor at h₂;
  cases h : List.find? ( fun B => !hasAcceptedDigest s a.1 B.d && B.parents.all fun pd => hasAcceptedDigest s a.1 pd ) s.blocks <;> simp_all +decide;
  · cases h' : List.find? ( fun B => hasAcceptedDigest s a.1 B.d && !hasStoredDigest s a.1 B.d ) s.blocks <;> simp_all +decide;
    · split_ifs at h₂ <;> simp_all +decide;
      · exact h₂ ▸ traceInv_of_doPropose system s a.1 a.2 ‹_› ( by aesop );
      · exact h₂ ▸ traceInv_of_doAdvance system s a.1 a.2 ( by assumption ) ( by aesop ) ( by assumption );
    · split_ifs at h₂ <;> simp_all +decide;
      · exact h₂ ▸ traceInv_of_doPropose system s a.1 a.2 ‹_› ( by aesop );
      · exact h₂ ▸ traceInv_of_doStore system s a.1 _ ‹_›;
  · split_ifs at h₂ <;> simp_all +decide;
    · exact h₂ ▸ traceInv_of_doPropose system s a.1 a.2 ‹_› ( by aesop );
    · exact h₂ ▸ traceInv_of_doAccept system s a.1 _ ‹_›

/-- The Beluga trace preserves admission well-formedness. -/
theorem belugaTrace_admissionWellFormed
    (system : BlockSynchroniserSystem) (k : Nat) :
    AdmissionWellFormed system (belugaTrace system k) := by
  suffices h : TraceInv system (belugaTrace system k) from h.1
  induction k with
  | zero => exact traceInv_init system
  | succ k ih => exact traceInv_step system _ ih

/-- Every `block_propose` op in the trace's emittedOperations
corresponds to a block in the pool (with matching author and round).
Extracted from the second `TraceInv` conjunct. -/
theorem belugaTrace_proposeOp_in_pool
    (system : BlockSynchroniserSystem) (k : Nat) :
    ∀ vid B r,
      ValidatorOperation.block_propose vid B r ∈ (belugaTrace system k).emittedOperations →
      B ∈ (belugaTrace system k).blocks ∧ B.author = vid ∧ B.r = r := by
  suffices h : TraceInv system (belugaTrace system k) from h.2.1
  induction k with
  | zero => exact traceInv_init system
  | succ k ih => exact traceInv_step system _ ih

end Beluga
end BlockSynchroniser