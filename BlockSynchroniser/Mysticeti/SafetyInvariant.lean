/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Trace invariants packaged for Mysticeti-Beluga safety (Appendix D.3).

`Mysticeti/Safety.lean` states the paper's L13/L15 against an abstract
`SystemState`; each of those lemmas takes four protocol-invariant
hypotheses (`AdmissionWellFormed`, `NoEquivocationInParents`, the
honest-author uniqueness assumption, and the authors-are-registered
side condition). For the executable `belugaTrace` instantiation, these
are not assumptions: three follow structurally from invariants already
established in `Beluga/AdmissionInvariant.lean` and `Beluga/Protocol.lean`,
and the fourth (`authorsValid`) is a one-line trace invariant about
emitted operations.

This module bundles the four facts as `MysticetiSafetyInv` and proves
the bundle for `belugaTrace`. `Mysticeti/Safety.lean` then provides
belugaTrace-specialised wrappers `lemma13_cert_persistence_belugaTrace`
and `lemma15_unique_cert_belugaTrace` whose only remaining hypotheses
are the genuine BFT side conditions (`hN`, `h_byz_bound`, `hids`) —
paper assumptions that cannot be derived from the executable trace.
-/
import Mathlib.Tactic
import BlockSynchroniser.Beluga.Patterns
import BlockSynchroniser.Beluga.AdmissionInvariant
import BlockSynchroniser.Beluga.Protocol

namespace BlockSynchroniser
namespace Mysticeti

open Beluga

/-- Trace invariants needed by Mysticeti-Beluga safety (Appendix D.3).

Bundles four facts that L13/L15 take as explicit hypotheses but that
hold of `belugaTrace` for free:

| field | corresponds to L13/L15 hypothesis |
|---|---|
| `admission` | `h_admission : AdmissionWellFormed system state` |
| `uniqueByAuthorRound` | `h_honest_unique` (in fact stronger — drops the honesty hypothesis) |
| `noEquivocation` | `h_no_eq : NoEquivocationInParents system state` |
| `authorsValid` | `h_authors_valid` |
-/
structure MysticetiSafetyInv (system : BlockSynchroniserSystem) (s : BelugaState) :
    Prop where
  /-- DAG admission well-formedness — closed in
  [`AdmissionInvariant.lean`](AdmissionInvariant.lean) by
  `belugaTrace_admissionWellFormed`. -/
  admission : AdmissionWellFormed system s
  /-- Author + round determine the block (paper §4.4). Stronger than
  L13's `h_honest_unique`: no honesty hypothesis is needed because
  `BlockInv.uniquePropose` is total. -/
  uniqueByAuthorRound :
    ∀ B₁ ∈ s.blocks, ∀ B₂ ∈ s.blocks,
      B₁.author = B₂.author → B₁.r = B₂.r → B₁ = B₂
  /-- Cross-block parent agreement (paper Appendix D.3 implicit fact). -/
  noEquivocation : NoEquivocationInParents system s
  /-- Every block author is a registered validator. -/
  authorsValid : ∀ B ∈ s.blocks, ∃ p ∈ system.validators, p.1 = B.author

/-- Structural derivation of the `uniqueByAuthorRound` conjunct from
`BlockInv`. No honesty hypothesis is required: `BlockInv.uniquePropose`
gives uniqueness of every `(author, round)` pair, honest or not. -/
private lemma uniqueByAuthorRound_of_blockInv
    {system : BlockSynchroniserSystem} {s : BelugaState}
    (h_inv : BlockInv system s) :
    ∀ B₁ ∈ s.blocks, ∀ B₂ ∈ s.blocks,
      B₁.author = B₂.author → B₁.r = B₂.r → B₁ = B₂ := by
  intro B₁ hB₁ B₂ hB₂ ha hr
  have hp₁ := h_inv.hasPropose B₁ hB₁
  have hp₂ := h_inv.hasPropose B₂ hB₂
  rw [ha, hr] at hp₁
  exact h_inv.uniquePropose _ _ _ _ hp₁ hp₂

/-- Structural derivation of `NoEquivocationInParents` from `BlockInv`.
The two parents-with-same-(author, round) are themselves blocks in
state, so `uniqueByAuthorRound_of_blockInv` applies directly. -/
private lemma noEquivocation_of_blockInv
    {system : BlockSynchroniserSystem} {s : BelugaState}
    (h_inv : BlockInv system s) :
    NoEquivocationInParents system s := by
  intro B₁ B₂ p₁ p₂ _ _ _ _ hp₁_in hp₂_in _ _ ha hr
  exact uniqueByAuthorRound_of_blockInv h_inv p₁ hp₁_in p₂ hp₂_in ha hr

/-! ## Helper lemmas for `authorsValid` -/

-- proof: aristotle (project c2ca4a2e) — mysticeti-safety-authorsValid round
/-- `updateValidator` preserves the list of validator IDs (first
components). -/
lemma updateValidator_validators_map_fst (s : BelugaState) (vid : ValidatorId)
    (f : BelugaValidator → BelugaValidator) :
    (updateValidator s vid f).validators.map Prod.fst = s.validators.map Prod.fst := by
  unfold updateValidator; aesop

-- proof: aristotle (project c2ca4a2e) — mysticeti-safety-authorsValid round
/-- `doAccept` preserves validator IDs. -/
lemma doAccept_validators_map_fst (s : BelugaState) (vid : ValidatorId) (B : Block) :
    (doAccept s vid B).validators.map Prod.fst = s.validators.map Prod.fst := by
  apply updateValidator_validators_map_fst

-- proof: aristotle (project c2ca4a2e) — mysticeti-safety-authorsValid round
/-- `doStore` preserves validator IDs. -/
lemma doStore_validators_map_fst (s : BelugaState) (vid : ValidatorId) (B : Block) :
    (doStore s vid B).validators.map Prod.fst = s.validators.map Prod.fst := by
  convert updateValidator_validators_map_fst s vid
    (fun bv => { bv with storedBlocks := B.d :: bv.storedBlocks }) using 1

-- proof: aristotle (project c2ca4a2e) — mysticeti-safety-authorsValid round
/-- `doAdvance` preserves validator IDs. -/
lemma doAdvance_validators_map_fst (s : BelugaState) (vid : ValidatorId) :
    (doAdvance s vid).validators.map Prod.fst = s.validators.map Prod.fst := by
  convert updateValidator_validators_map_fst s vid
    (fun bv => { bv with currentRound := bv.currentRound + 1 }) using 1

/-- `doAccept` does not change the block list. -/
lemma doAccept_blocks (s : BelugaState) (vid : ValidatorId) (B : Block) :
    (doAccept s vid B).blocks = s.blocks := by
  unfold doAccept updateValidator; rfl

/-- `doStore` does not change the block list. -/
lemma doStore_blocks (s : BelugaState) (vid : ValidatorId) (B : Block) :
    (doStore s vid B).blocks = s.blocks := by
  unfold doStore updateValidator; rfl

/-- `doAdvance` does not change the block list. -/
lemma doAdvance_blocks (s : BelugaState) (vid : ValidatorId) :
    (doAdvance s vid).blocks = s.blocks := by
  unfold doAdvance updateValidator; rfl

-- proof: aristotle (project c2ca4a2e) — mysticeti-safety-authorsValid round
/-- `doPropose` prepends exactly one block with `author = vid`, leaving
the rest of the block list unchanged. -/
lemma doPropose_blocks (system : BlockSynchroniserSystem) (s : BelugaState)
    (vid : ValidatorId) (r : Round) :
    ∃ B, (doPropose system s vid r).blocks = B :: s.blocks ∧ B.author = vid := by
  exact ⟨_, rfl, rfl⟩

-- proof: aristotle (project c2ca4a2e) — mysticeti-safety-authorsValid round
/-- `doPropose` does not change validator IDs. -/
lemma doPropose_validators_map_fst (system : BlockSynchroniserSystem) (s : BelugaState)
    (vid : ValidatorId) (r : Round) :
    (doPropose system s vid r).validators.map Prod.fst = s.validators.map Prod.fst := by
  unfold doPropose; aesop

-- proof: aristotle (project c2ca4a2e) — mysticeti-safety-authorsValid round
set_option maxHeartbeats 800000 in
/-- Every block in `step system s` is either already in `s.blocks` or has
its author among the first components of `s.validators`. -/
lemma step_blocks_mem (system : BlockSynchroniserSystem) (s : BelugaState) (B : Block) :
    B ∈ (step system s).blocks →
    B ∈ s.blocks ∨ B.author ∈ s.validators.map Prod.fst := by
  unfold step
  cases h : List.findSome? (fun x => tryActFor system s x.1 x.2) s.validators <;>
    simp_all +decide
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨l₁, a, l₂, h₁, h₂, h₃⟩ := h
  unfold tryActFor at h₂
  cases h : List.find? (fun B => !hasAcceptedDigest s a.1 B.d &&
      B.parents.all fun pd => hasAcceptedDigest s a.1 pd) s.blocks <;>
    simp_all +decide
  · cases h : List.find? (fun B => hasAcceptedDigest s a.1 B.d &&
        !hasStoredDigest s a.1 B.d) s.blocks <;> simp_all +decide
    · split_ifs at h₂ <;> simp_all +decide [doPropose, doAccept, doStore, doAdvance]
      · grind
      · unfold updateValidator at h₂; aesop
    · split_ifs at h₂ <;> simp_all +decide [doPropose, doStore]
      · grind
      · unfold updateValidator at h₂; aesop
  · split_ifs at h₂ <;> simp_all +decide [doPropose, doAccept]
    · grind
    · unfold updateValidator at h₂; aesop

/-- The validator IDs of the initial state correspond to entries in
`system.validators`. -/
lemma init_validators_ids (system : BlockSynchroniserSystem) :
    ∀ vid ∈ (BelugaState.init system).validators.map Prod.fst,
      ∃ p ∈ system.validators, p.1 = vid := by
  intro vid hvid
  unfold BelugaState.init at hvid
  simp only [List.map_map, Function.comp, List.mem_map] at hvid
  obtain ⟨pair, hpair_mem, hpair_eq⟩ := hvid
  exact ⟨pair, hpair_mem, hpair_eq⟩

-- proof: aristotle (project c2ca4a2e) — mysticeti-safety-authorsValid round
/-- The `authorsValid` conjunct holds for every step of the Beluga
trace; jointly with the validator-IDs-stable invariant, this is the
right inductive carrier. -/
private lemma authorsValid_trace
    (system : BlockSynchroniserSystem) (k : Nat) :
    (∀ B ∈ (belugaTrace system k).blocks, ∃ p ∈ system.validators, p.1 = B.author) ∧
    (∀ vid ∈ (belugaTrace system k).validators.map Prod.fst,
      ∃ p ∈ system.validators, p.1 = vid) := by
  induction' k with k ih
  · exact ⟨by tauto, init_validators_ids system⟩
  · have h_step_validators :
        (step system (belugaTrace system k)).validators.map Prod.fst =
          (belugaTrace system k).validators.map Prod.fst := by
      unfold step
      cases h : List.findSome? (fun x =>
          tryActFor system (belugaTrace system k) x.1 x.2)
          (belugaTrace system k).validators <;>
        simp +decide [h]
      have h_step_validators :
          ∀ (s : BelugaState) (vid : ValidatorId) (bv : BelugaValidator),
            (tryActFor system (belugaTrace system k) vid bv = some s) →
            (s.validators.map Prod.fst =
              (belugaTrace system k).validators.map Prod.fst) := by
        intros s vid bv hact
        unfold tryActFor at hact
        cases h : List.find? (fun B =>
            !hasAcceptedDigest (belugaTrace system k) vid B.d &&
            B.parents.all fun pd =>
              hasAcceptedDigest (belugaTrace system k) vid pd)
            (belugaTrace system k).blocks <;>
          simp +decide [h] at hact ⊢
        · cases h' : List.find? (fun B =>
              hasAcceptedDigest (belugaTrace system k) vid B.d &&
              !hasStoredDigest (belugaTrace system k) vid B.d)
              (belugaTrace system k).blocks <;>
            simp +decide [h'] at hact ⊢
          · split_ifs at hact <;>
              simp_all +decide [doPropose_validators_map_fst,
                doAdvance_validators_map_fst]
            · exact hact ▸ doPropose_validators_map_fst _ _ _ _
            · exact hact ▸ doAdvance_validators_map_fst _ _
          · split_ifs at hact <;>
              simp_all +decide [doPropose_validators_map_fst,
                doStore_validators_map_fst]
            · exact hact ▸ doPropose_validators_map_fst _ _ _ _
            · exact hact ▸ doStore_validators_map_fst _ _ _
        · split_ifs at hact <;>
            simp_all +decide [doPropose_validators_map_fst,
              doAccept_validators_map_fst]
          · exact hact ▸ doPropose_validators_map_fst _ _ _ _
          · exact hact ▸ doAccept_validators_map_fst _ _ _
      rw [List.findSome?_eq_some_iff] at h
      aesop
    refine ⟨?_, ?_⟩
    · intro B hB
      have := step_blocks_mem system (belugaTrace system k) B hB
      aesop
    · exact fun x hx => ih.2 x <| h_step_validators ▸ hx

/-- The Beluga trace satisfies the Mysticeti safety invariant bundle.

All four conjuncts are proved:
- `admission` ← `belugaTrace_admissionWellFormed`,
- `uniqueByAuthorRound` ← `blockInv_trace` + `BlockInv.uniquePropose`,
- `noEquivocation` ← `blockInv_trace` + `BlockInv.uniquePropose`,
- `authorsValid` ← Nat induction via `authorsValid_trace`, which
  threads a joint blocks-+-validator-IDs carrier (only `doPropose`
  adds blocks, and the validator-ID list is preserved by every
  `tryActFor` branch). -/
theorem belugaTrace_satisfies_mysticetiSafetyInv
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (k : Nat) :
    MysticetiSafetyInv system (belugaTrace system k) := by
  have h_blockInv := blockInv_trace system hids k
  refine
    { admission := belugaTrace_admissionWellFormed system k
      uniqueByAuthorRound := uniqueByAuthorRound_of_blockInv h_blockInv
      noEquivocation := noEquivocation_of_blockInv h_blockInv
      authorsValid := (authorsValid_trace system k).1 }

end Mysticeti
end BlockSynchroniser
