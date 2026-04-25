/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Step-preservation lemmas: the executable `step` function preserves
validator membership and reputation tables. Used by Lemma 3 (honest
validators are not blamed).
-/
import Mathlib.Tactic
import BlockSynchroniser.Beluga.Protocol
import BlockSynchroniser.Lib.Basic

namespace BlockSynchroniser.Beluga

/-! ## updateValidator preserves getValidator and reputation -/

/-
`updateValidator` preserves `getValidator` for any validator,
provided the update function preserves the `reputation` field.
-/
lemma updateValidator_getValidator_reputation (s : BelugaState) (vid actor : ValidatorId)
    (f : BelugaValidator → BelugaValidator) (bv : BelugaValidator)
    (h : s.getValidator vid = some bv)
    (hf : ∀ bv, (f bv).reputation = bv.reputation) :
    ∃ bv', (updateValidator s actor f).getValidator vid = some bv' ∧
      bv'.reputation = bv.reputation := by
  simp_all +decide [ updateValidator ];
  unfold BelugaState.getValidator at h ⊢; simp_all +decide [ List.find?_eq_some_iff_append, List.find?_cons ] ;
  grind

/-! ## tryActFor preserves getValidator and reputation -/

/-
Every state produced by `tryActFor` preserves `getValidator` and
reputation for all validators.
-/
lemma tryActFor_preserves_reputation (system : BlockSynchroniserSystem) (s : BelugaState)
    (vid_actor : ValidatorId) (bv_actor : BelugaValidator) (vid : ValidatorId) (bv : BelugaValidator)
    (h : s.getValidator vid = some bv) (s' : BelugaState)
    (h' : tryActFor system s vid_actor bv_actor = some s') :
    ∃ bv', s'.getValidator vid = some bv' ∧ bv'.reputation = bv.reputation := by
  -- proof: aristotle (project 91c97602) — partial; ▸ + heartbeat issue, queued for round 3e-followup
  sorry

/-! ## step preserves getValidator and reputation -/

/-
The main step function preserves `getValidator` and reputation
for all validators.
-/
theorem step_getValidator_reputation (system : BlockSynchroniserSystem) (s : BelugaState)
    (vid : ValidatorId) (bv : BelugaValidator)
    (h : s.getValidator vid = some bv) :
    ∃ bv', (step system s).getValidator vid = some bv' ∧
      bv'.reputation = bv.reputation := by
  unfold step;
  cases h' : List.findSome? ( fun x => tryActFor system s x.1 x.2 ) s.validators <;> simp_all +decide;
  obtain ⟨ vid_actor, bv_actor, h_actor ⟩ := Lib.findSome_witness s.validators ( fun x => tryActFor system s x.1 x.2 ) _ h';
  apply tryActFor_preserves_reputation system s vid_actor.1 vid_actor.2 vid bv h _ h_actor

/-! ## belugaTrace preserves getValidator and reputation -/

/-
Across trace steps, `getValidator` reputation is preserved.
-/
theorem belugaTrace_getValidator_reputation (system : BlockSynchroniserSystem)
    (vid : ValidatorId) (k : Nat) (bv : BelugaValidator)
    (h : (belugaTrace system k).getValidator vid = some bv)
    (k' : Nat) (hk : k ≤ k') :
    ∃ bv', (belugaTrace system k').getValidator vid = some bv' ∧
      bv'.reputation = bv.reputation := by
  induction' hk with k hk ih generalizing bv;
  · exact ⟨ bv, h, rfl ⟩;
  · exact ih bv h |> fun ⟨ bv', hv₁, hv₂ ⟩ => by have := step_getValidator_reputation system ( belugaTrace system k ) vid bv' hv₁; aesop;

/-! ## Honest validators exist at every trace step -/

/-
Honest validators have a `getValidator` entry in the initial state.
-/
theorem init_getValidator_honest (system : BlockSynchroniserSystem) (vid : ValidatorId)
    (h : isHonestValidator system vid = true) :
    ∃ bv, (BelugaState.init system).getValidator vid = some bv := by
  -- By definition of `isHonest`, if `isHonest system vid` is true, then `system.validators.find? (fun (vid', _) => vid' = vid)` returns `some (vid, true)`.
  have h_find : system.validators.find? (fun (vid', _) => vid' = vid) = some (vid, true) := by
    unfold isHonestValidator at h;
    unfold BlockSynchroniserSystem.isHonest at h;
    grind;
  -- proof: aristotle (project 91c97602)
  unfold BelugaState.getValidator; simp +decide [ BelugaState.init ] ;
  use vid; simp_all +decide [ Function.comp ] ;
  exact Or.inr h_find

/-
Honest validators have a `getValidator` entry at every trace step.
-/
theorem belugaTrace_getValidator_honest (system : BlockSynchroniserSystem) (vid : ValidatorId)
    (h : isHonestValidator system vid = true) (k : Nat) :
    ∃ bv, (belugaTrace system k).getValidator vid = some bv := by
  -- proof: aristotle (project 91c97602)
  induction' k with k ih;
  · exact init_getValidator_honest system vid h;
  · exact step_getValidator_reputation system ( belugaTrace system k ) vid _ ih.choose_spec |> fun h => by tauto;

end BlockSynchroniser.Beluga