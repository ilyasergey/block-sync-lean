/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Beluga's main theorems (paper §5).

The four main theorems (T1–T4) and supporting Lemmas 1–2 are stated
against `belugaTrace`. They are parameterised by a paper-implicit
**scheduler-fairness assumption** that is required to recover the
paper's 3Δ latency bounds; see
[`docs/paper-feedback-l1-l2-fairness.md`](../../docs/paper-feedback-l1-l2-fairness.md)
for a full discussion (paper terminology, no Lean) and
[`formalization.md`](../../formalization.md) "Mechanization findings"
for the project-side summary.
-/
import Mathlib.Tactic
import BlockSynchroniser.System
import BlockSynchroniser.Properties
import BlockSynchroniser.Timing
import BlockSynchroniser.Beluga.Protocol
import BlockSynchroniser.Beluga.AdmissionInvariant

namespace BlockSynchroniser
namespace Beluga
namespace Theorems

open Properties

/-! ## Section 5 — Main theorems

Each theorem says "the trace induced by Beluga's executable protocol
satisfies Definition 1.X". The statements are stated against the
*relational* `HonestStep` semantics — `belugaTrace` (the executable
schedule) is one specific witness, but the theorems generalize to any
trace whose every step satisfies `HonestStep`. -/

/-! ### Scheduler fairness (paper Assumption 2, made explicit — lockstep variant)

The paper's prose proofs of L1, L2, and T1–T4 silently assume that
honest validators *act promptly*: whenever the protocol of §4 enables
a local action (propose/accept/store/advance), an honest validator
performs it within `Δ`. Without this, the paper's `3Δ`-bounded round
synchronisation (and any "eventually" claim downstream) does not
hold — see `docs/paper-feedback-l1-l2-fairness.md` for a paper-level
counterexample.

We surface the assumption at *round granularity* (which is what our
trace model exposes), in the **lockstep** form actually needed by L2:
post-GST, when some honest validator reaches round `r`, every honest
validator reaches round `r + 1` within `3Δ`. The `+1` (rather than
`≥ r`) captures the combined effect of the §4 `allProposedFor` gate
and per-action scheduler fairness: in `3Δ` not only does everyone
catch up to the leader's round, but the leader also advances. This
is finding **F-1a** in `docs/mechanization-findings.md`.

Discharging this from a more primitive scheduler model would require
adding action-level enabledness predicates to our trace (future work).
-/
def SchedulerFairness
    (system : BlockSynchroniserSystem) (time : TimeMap) : Prop :=
  ∀ k r,
    time k ≥ system.GST →
    (∃ vid bv,
        isHonestValidator system vid = true ∧
        (belugaTrace system k).getValidator vid = some bv ∧
        bv.currentRound = r) →
    ∃ k', k ≤ k' ∧ time k' ≤ time k + 3 * system.Δ ∧
      ∀ vid, isHonestValidator system vid = true →
        ∃ bv, (belugaTrace system k').getValidator vid = some bv ∧
              bv.currentRound ≥ r + 1

/-! ## Helper lemmas — paper-faithful infrastructure

These lemmas establish basic invariants of the executable `step`
function: validator persistence, round monotonicity, action-level
preservation. They are independent of the fairness assumption above
and are reused throughout the proofs of L1–L2 and T1–T4. -/

/--
If `vid` is honest in `system`, then `vid` appears in `system.validators`
with `isHonest = true`.
-/
lemma honest_validator_in_system (system : BlockSynchroniserSystem) (vid : ValidatorId)
    (h : isHonestValidator system vid = true) :
    ∃ p ∈ system.validators, p.1 = vid ∧ p.2 = true := by
  unfold isHonestValidator at h
  unfold BlockSynchroniserSystem.isHonest at h
  grind

/--
`List.find?` with `BEq` agrees with `List.find?` with `=` for `Nat`.
-/
lemma find_beq_eq_find {α : Type} (l : List (Nat × α)) (vid : Nat) :
    l.find? (fun (id, _) => id == vid) = l.find? (fun (id, _) => decide (id = vid)) := by
  grind

/--
If `vid` is honest, then `getValidator` on the initial state returns `some`.
-/
lemma getValidator_init_some (system : BlockSynchroniserSystem) (vid : ValidatorId)
    (h : isHonestValidator system vid = true) :
    ∃ bv, (BelugaState.init system).getValidator vid = some bv := by
  have h_map : (List.map (fun (vid, _) =>
      (vid, { reputation := ReputationTable.init system : BelugaValidator }))
      system.validators).find? (fun (id, _) => id == vid) ≠ none := by
    obtain ⟨ p, hp ⟩ := honest_validator_in_system system vid h
    grind
  exact Option.ne_none_iff_exists'.mp h_map |> fun ⟨ x, hx ⟩ => ⟨ _, congr_arg _ hx ⟩

/--
Every validator in the initial state has `currentRound = 0`.
-/
lemma getValidator_init_round_zero (system : BlockSynchroniserSystem) (vid : ValidatorId)
    (bv : BelugaValidator)
    (h : (BelugaState.init system).getValidator vid = some bv) :
    bv.currentRound = 0 := by
  simp [BelugaState.getValidator, BelugaState.init] at h
  cases h.2; aesop

-- proof: aristotle (project b544affb) — theorems-helpers round
/--
`updateValidator` preserves `getValidator vid = none`.
-/
lemma updateValidator_none (s : BelugaState) (vid vid' : ValidatorId)
    (f : BelugaValidator → BelugaValidator) :
    (updateValidator s vid' f).getValidator vid = none → s.getValidator vid = none := by
  unfold updateValidator BelugaState.getValidator
  simp +decide
  intro h; by_contra hc; push_neg at hc
  obtain ⟨a, b, hmem, rfl⟩ := hc
  have := h a b hmem
  split_ifs at this <;> simp at this

/-
The `step` function preserves the validator ID list.

Proof: structural case analysis on `tryActFor`'s four branches.
-/
-- proof: aristotle (project b544affb) — theorems-helpers round
set_option maxHeartbeats 800000 in
lemma step_preserves_validator_ids (system : BlockSynchroniserSystem) (s : BelugaState) (vid : ValidatorId) :
    (step system s).getValidator vid = none → s.getValidator vid = none := by
  unfold step;
  cases h : List.findSome? ( fun x => tryActFor system s x.1 x.2 ) s.validators <;> simp_all +decide;
  have h_findSome : ∃ x ∈ s.validators, tryActFor system s x.1 x.2 = some ‹_› := by
    rw [List.findSome?_eq_some_iff] at h
    obtain ⟨l₁, a, l₂, hl, hf, _⟩ := h
    exact ⟨a, by simp [hl], hf⟩
  obtain ⟨ x, hx₁, hx₂ ⟩ := h_findSome;
  unfold tryActFor at hx₂;
  cases h : List.find? ( fun B => !hasAcceptedDigest s x.1 B.d && B.parents.all fun pd => hasAcceptedDigest s x.1 pd ) s.blocks <;> simp_all +decide;
  · cases h' : List.find? ( fun B => hasAcceptedDigest s x.1 B.d && !hasStoredDigest s x.1 B.d ) s.blocks <;> simp_all +decide;
    · split_ifs at hx₂ <;> simp_all +decide [ doPropose, doAdvance ];
      · unfold BelugaState.getValidator; aesop;
      · grind +suggestions;
    · split_ifs at hx₂ <;> simp_all +decide [ doPropose, doStore ];
      · unfold BelugaState.getValidator; aesop;
      · unfold BelugaState.getValidator at *; simp_all +decide [ updateValidator ] ;
        grind;
  · unfold doAccept at hx₂; simp_all +decide [ updateValidator ] ;
    unfold doPropose at hx₂; simp_all +decide [ BelugaState.getValidator ] ;
    grind

/--
If a validator is present at step `k`, it is present at step `k+1`.
-/
lemma getValidator_persistent (system : BlockSynchroniserSystem) (vid : ValidatorId) (k : Nat) :
    (∃ bv, (belugaTrace system k).getValidator vid = some bv) →
    (∃ bv, (belugaTrace system (k+1)).getValidator vid = some bv) := by
  contrapose!
  intro h bv hv
  convert step_preserves_validator_ids system (belugaTrace system k) vid _
  · aesop
  · exact Option.eq_none_iff_forall_ne_some.mpr h

/--
`updateValidator` preserves `getValidator` for other validator IDs.
-/
lemma updateValidator_getValidator_ne (s : BelugaState) (vid vid' : ValidatorId)
    (f : BelugaValidator → BelugaValidator) (h : vid ≠ vid') :
    (updateValidator s vid' f).getValidator vid = s.getValidator vid := by
  unfold updateValidator BelugaState.getValidator
  induction s.validators <;> simp +decide [*]
  grind

/--
`updateValidator` applies `f` to the target validator.
-/
lemma updateValidator_getValidator_eq (s : BelugaState) (vid : ValidatorId)
    (f : BelugaValidator → BelugaValidator) (bv : BelugaValidator)
    (h : s.getValidator vid = some bv) :
    (updateValidator s vid f).getValidator vid = some (f bv) := by
  unfold BelugaState.getValidator at *
  unfold updateValidator; simp +decide
  rw [Option.map_eq_some_iff] at h
  grind +suggestions

/--
`doPropose` does not change `getValidator`.
-/
lemma doPropose_getValidator (system : BlockSynchroniserSystem) (s : BelugaState)
    (vid vid' : ValidatorId) (r : Round) :
    (doPropose system s vid' r).getValidator vid = s.getValidator vid := by
  exact (Option.map_inj_right fun x y a => a).mp rfl

/--
Changing only `emittedOperations` doesn't affect `getValidator`.
-/
lemma getValidator_emittedOperations_irrelevant (s : BelugaState) (ops : List ValidatorOperation)
    (vid : ValidatorId) :
    ({ s with emittedOperations := ops } : BelugaState).getValidator vid = s.getValidator vid := by
  unfold BelugaState.getValidator; aesop

/--
`doAccept` preserves `currentRound` for all validators.
-/
lemma doAccept_round (s : BelugaState) (vid vid' : ValidatorId) (B : Block)
    (bv : BelugaValidator) (h : s.getValidator vid = some bv) :
    ∃ bv', (doAccept s vid' B).getValidator vid = some bv' ∧
           bv'.currentRound = bv.currentRound := by
  by_cases h' : vid = vid' <;> simp_all +decide [doAccept]
  · exact ⟨ _, updateValidator_getValidator_eq _ _ _ _ h, rfl ⟩
  · rw [updateValidator_getValidator_ne]; aesop
    assumption

/--
`doStore` preserves `currentRound` for all validators.
-/
lemma doStore_round (s : BelugaState) (vid vid' : ValidatorId) (B : Block)
    (bv : BelugaValidator) (h : s.getValidator vid = some bv) :
    ∃ bv', (doStore s vid' B).getValidator vid = some bv' ∧
           bv'.currentRound = bv.currentRound := by
  by_cases h' : vid = vid'
  · subst h'
    exact ⟨ _, updateValidator_getValidator_eq s vid
              (fun bv => { bv with storedBlocks := B.d :: bv.storedBlocks }) bv h, rfl ⟩
  · unfold doStore
    simp +decide [*, getValidator_emittedOperations_irrelevant, updateValidator_getValidator_ne]

/--
`doAdvance` for `vid'` preserves or increments `currentRound` for `vid`.
-/
lemma doAdvance_round (s : BelugaState) (vid vid' : ValidatorId)
    (bv : BelugaValidator) (h : s.getValidator vid = some bv) :
    ∃ bv', (doAdvance s vid').getValidator vid = some bv' ∧
           bv.currentRound ≤ bv'.currentRound := by
  by_cases h' : vid = vid' <;> simp_all +decide [doAdvance]
  · exact ⟨ _, updateValidator_getValidator_eq _ _ _ _ h, Nat.le_succ _ ⟩
  · exact ⟨ bv, by rw [updateValidator_getValidator_ne _ _ _ _ h']; assumption,
           by simp +decide ⟩

/-
The `step` function never decreases any validator's `currentRound`.

Proof: structural case analysis on `tryActFor`'s four branches via the
per-action helpers `doAccept_round`, `doStore_round`, `doAdvance_round`,
`doPropose_getValidator`.
-/
-- proof: aristotle (project b544affb) — theorems-helpers round
set_option maxHeartbeats 800000 in
lemma step_round_monotone (system : BlockSynchroniserSystem) (s : BelugaState) (vid : ValidatorId)
    (bv bv' : BelugaValidator)
    (h : s.getValidator vid = some bv)
    (h' : (step system s).getValidator vid = some bv') :
    bv.currentRound ≤ bv'.currentRound := by
  unfold step at h';
  cases h'' : List.findSome? ( fun x => tryActFor system s x.1 x.2 ) s.validators <;> simp_all +decide;
  rw [ List.findSome?_eq_some_iff ] at h'';
  obtain ⟨ l₁, a, l₂, h₁, h₂, h₃ ⟩ := h'';
  unfold tryActFor at h₂;
  cases h : List.find? ( fun B => !hasAcceptedDigest s a.1 B.d && B.parents.all fun pd => hasAcceptedDigest s a.1 pd ) s.blocks <;> simp_all +decide;
  · split_ifs at h₂;
    · grind +suggestions;
    · cases h : List.find? ( fun B => hasAcceptedDigest s a.1 B.d && !hasStoredDigest s a.1 B.d ) s.blocks <;> simp_all +decide;
      · subst h₂;
        unfold doAdvance at h';
        grind +suggestions;
      · have := doStore_round s vid a.1 ‹_› bv ‹_›; aesop;
    · cases h : List.find? ( fun B => hasAcceptedDigest s a.1 B.d && !hasStoredDigest s a.1 B.d ) s.blocks <;> simp_all +decide;
      have := doStore_round s vid a.1 ‹_› bv ‹_›; aesop;
  · split_ifs at h₂ ; simp_all +decide [ doPropose ];
    · unfold BelugaState.getValidator at *;
      grind;
    · have := doAccept_round s vid a.1 ‹_› bv ‹_›; aesop;


/-! ## Liveness-support helper lemmas

These lemmas establish structural properties of the trace that are
needed by the post-GST liveness bundle proof — in particular the
*intermediate-value theorem* for rounds (`round_intermediate_value`),
which underpins the L2 derivation from the lockstep `SchedulerFairness`.

-/

/-
`doAdvance` for `vid'` sets `currentRound` to `bv.currentRound + 1` for
the target validator, and leaves other validators unchanged. In either
case the new round is at most `bv.currentRound + 1`.
-/
-- proof: aristotle (project 4f618efb) — beluga-§5-bundle round
lemma doAdvance_round_at_most_one (s : BelugaState) (vid vid' : ValidatorId)
    (bv : BelugaValidator) (h : s.getValidator vid = some bv) :
    ∃ bv', (doAdvance s vid').getValidator vid = some bv' ∧
           bv'.currentRound ≤ bv.currentRound + 1 := by
  by_cases h : vid = vid';
  · subst h;
    exact ⟨ _, updateValidator_getValidator_eq _ _ _ _ h, by simp +decide ⟩;
  · have h_getValidator_ne : (doAdvance s vid').getValidator vid = s.getValidator vid := by
      exact updateValidator_getValidator_ne s vid vid' ( fun bv => { bv with currentRound := bv.currentRound + 1 } ) h;
    aesop

/-
The `step` function increases any validator's `currentRound` by at most 1.
-/
-- proof: aristotle (project 4f618efb) — beluga-§5-bundle round
set_option maxHeartbeats 800000 in
lemma step_round_at_most_one (system : BlockSynchroniserSystem) (s : BelugaState)
    (vid : ValidatorId) (bv bv' : BelugaValidator)
    (h : s.getValidator vid = some bv)
    (h' : (step system s).getValidator vid = some bv') :
    bv'.currentRound ≤ bv.currentRound + 1 := by
  revert s;
  unfold step;
  intro s hs hs'; rcases h : List.findSome? ( fun x => tryActFor system s x.1 x.2 ) s.validators with ( _ | s' ) <;> simp_all +decide ;
  rw [ List.findSome?_eq_some_iff ] at h;
  obtain ⟨ l₁, a, l₂, h₁, h₂, h₃ ⟩ := h;
  unfold tryActFor at h₂;
  cases h : List.find? ( fun B => !hasAcceptedDigest s a.1 B.d && B.parents.all fun pd => hasAcceptedDigest s a.1 pd ) s.blocks <;> simp_all +decide;
  · cases h : List.find? ( fun B => hasAcceptedDigest s a.1 B.d && !hasStoredDigest s a.1 B.d ) s.blocks <;> simp_all +decide;
    · split_ifs at h₂ <;> simp_all +decide [ doPropose, doAdvance ];
      · unfold BelugaState.getValidator at hs';
        unfold BelugaState.getValidator at hs; simp_all +decide [ List.find?_append ] ;
        grind;
      · grind +suggestions;
    · split_ifs at h₂ <;> simp_all +decide [ doPropose, doStore ];
      · unfold BelugaState.getValidator at hs hs';
        grind;
      · grind +suggestions;
  · split_ifs at h₂ <;> simp_all +decide;
    · unfold doPropose at h₂;
      unfold BelugaState.getValidator at *;
      grind;
    · have := doAccept_round s vid a.1 ‹_› bv hs; aesop;

/-
Honest validators are present at every trace step.
-/
-- proof: aristotle (project 4f618efb) — beluga-§5-bundle round
lemma honest_validator_persistent_trace (system : BlockSynchroniserSystem)
    (vid : ValidatorId) (hvid : isHonestValidator system vid = true) (k : Nat) :
    ∃ bv, (belugaTrace system k).getValidator vid = some bv := by
  exact Nat.recOn k ( getValidator_init_some system vid hvid ) fun n ihn => getValidator_persistent _ _ _ ihn

/-
Round monotonicity across arbitrary trace steps:
if `k₁ ≤ k₂` and `vid` is present at both steps, its round does not decrease.
-/
-- proof: aristotle (project 4f618efb) — beluga-§5-bundle round
lemma round_monotone_trace (system : BlockSynchroniserSystem) (vid : ValidatorId)
    (k₁ k₂ : Nat) (hle : k₁ ≤ k₂)
    (bv₁ bv₂ : BelugaValidator)
    (h₁ : (belugaTrace system k₁).getValidator vid = some bv₁)
    (h₂ : (belugaTrace system k₂).getValidator vid = some bv₂) :
    bv₁.currentRound ≤ bv₂.currentRound := by
  have h_ind : ∀ k₁ k₂, k₁ ≤ k₂ → ∀ (bv₁ bv₂ : BelugaValidator),
      (Beluga.belugaTrace system k₁).getValidator vid = some bv₁ →
      (Beluga.belugaTrace system k₂).getValidator vid = some bv₂ →
      bv₁.currentRound ≤ bv₂.currentRound := by
    intros k₁ k₂ hle bv₁ bv₂ h₁ h₂;
    induction' hle with k₂ hk₂ ih generalizing bv₂;
    · grind;
    · obtain ⟨bv₂', hb₂'⟩ : ∃ bv₂', (Beluga.belugaTrace system k₂).getValidator vid = some bv₂' := by
        have h_persistent : ∀ k, (∃ bv, (Beluga.belugaTrace system k).getValidator vid = some bv) →
            (∃ bv, (Beluga.belugaTrace system (k + 1)).getValidator vid = some bv) := by
          exact fun k a => getValidator_persistent system vid k a;
        exact Nat.le_induction ( by tauto ) ( fun k hk ih => by tauto ) k₂ hk₂;
      exact le_trans ( ih _ hb₂' ) ( step_round_monotone system _ _ _ _ hb₂' h₂ );
  exact h_ind k₁ k₂ hle bv₁ bv₂ h₁ h₂

/-
Intermediate-value theorem for validator rounds.

If `vid` is at round `≤ r` at step `k₁` and at round `≥ r` at step
`k₂ ≥ k₁`, then there is a step `k ∈ [k₁, k₂]` where `vid` is at
exactly round `r`.

Proof sketch: induction on `k₂ − k₁`. If `k₁ = k₂`, the result is
immediate. Otherwise look at `vid`'s round at step `k₂ − 1`: if it
is `≥ r`, recurse on `[k₁, k₂ − 1]`; if it is `< r`, then since
`step` changes the round by at most 1, the round at `k₂` is
`≤ (round at k₂ − 1) + 1 ≤ r`, which combined with `≥ r` gives
exactly `r`.
-/
-- proof: aristotle (project 4f618efb) — beluga-§5-bundle round
lemma round_intermediate_value (system : BlockSynchroniserSystem) (vid : ValidatorId)
    (k₁ k₂ : Nat) (r : Nat)
    (hle : k₁ ≤ k₂)
    (bv₁ bv₂ : BelugaValidator)
    (h₁ : (belugaTrace system k₁).getValidator vid = some bv₁)
    (h₂ : (belugaTrace system k₂).getValidator vid = some bv₂)
    (hr₁ : bv₁.currentRound ≤ r)
    (hr₂ : r ≤ bv₂.currentRound) :
    ∃ k, k₁ ≤ k ∧ k ≤ k₂ ∧
      ∃ bv, (belugaTrace system k).getValidator vid = some bv ∧
            bv.currentRound = r := by
  induction' hle with k₂ hk ih generalizing bv₁ bv₂ <;> simp_all +decide;
  · exact ⟨ k₁, le_rfl, le_rfl, bv₁, h₂, le_antisymm hr₁ hr₂ ⟩;
  · obtain ⟨bv_prev, hbv_prev⟩ : ∃ bv_prev, (belugaTrace system k₂).getValidator vid = some bv_prev := by
      have h_persistent : ∀ k, (∃ bv, (belugaTrace system k).getValidator vid = some bv) →
          (∃ bv, (belugaTrace system (k + 1)).getValidator vid = some bv) := by
        exact fun k a => getValidator_persistent system vid k a;
      exact Nat.le_induction ( by tauto ) ( fun k hk ih => h_persistent k ih ) k₂ hk;
    have h_step : bv₂.currentRound ≤ bv_prev.currentRound + 1 := by
      apply step_round_at_most_one;
      exact hbv_prev;
      exact h₂;
    grind +splitImp

/-! ## Structural invariants for the §5 bundle proof

The post-GST liveness conjuncts (T1, T3, T4) rely on a key
structural fact about `tryActFor`'s priority order: validator `vid`
can only advance from round `r-1` to round `r` after it has
proposed for round `r-1` (priority gate `if !hasProposedFor` puts
propose strictly before advance). By induction, a validator at
round `r` has proposed for every round `r' < r`.

This invariant + iterated `SchedulerFairness` is enough to derive
T3 (every round eventually has 2f+1 proposers); similar
structural arguments handle T1 and T4 once we add invariants
for accept-before-advance and store-before-advance.

L1 (`honest_round_sync`) is weakened from the paper's strict
same-round form to the lockstep-progress form; finding **F-1b**
records the gap-1 transient states between adjacent round advances
that block the strict form. -/

/-! ### Side conditions threaded through the bundle

Two paper-§2 side conditions surface in nearly every theorem in
this file. Naming them lets the public signatures stay readable
and centralizes their justification. -/

/-- BFT honest-count side condition (paper §2). T3 (round_progression)
and T4 (round_termination) both need to count `2f + 1` distinct
honest validators that propose / accept; the bundle is vacuously
satisfied otherwise (`SchedulerFairness` ranges over honest
validators but is trivial when the honest set is empty).

We take the **lower-bound form** `≥ 2 * f + 1` rather than the
exact `= 2 * f + 1` form the rest of the project tends to use:
- Paper §2 only commits to `f < n / 3` (Byzantine strictly
  fewer than a third), from which honest count is `n - f > 2f`,
  i.e., honest ≥ 2f + 1.
- The exact equality follows only under F-2's pinning of
  `n = 3f + 1` (a notational tightening we recommend the paper
  adopt, but not yet committed to globally in this bundle).
- T3 / T4 only need the lower bound (counting argument).
Using `≥` keeps the bundle independent of F-2's pinning while
still being directly supported by the paper text. -/
abbrev HonestBFTBound (system : BlockSynchroniserSystem) : Prop :=
  (system.validators.filter (fun p => p.2 = true)).length ≥ 2 * system.f + 1

/-- Paper §2 implicit: validator IDs are distinct (one record per
registered validator). Threaded through the trace via
`belugaTrace_validators_nodup`. Needed by T3/T4 to identify
the `findSome?` actor with the `find?`-target. -/
abbrev ValidatorsNodup (system : BlockSynchroniserSystem) : Prop :=
  (system.validators.map Prod.fst).Nodup

/-
Operations emitted by `step` only grow `emittedOperations` (monotone).
Specifically, every operation in `s.emittedOperations` is also in
`(step system s).emittedOperations`.
-/
set_option maxHeartbeats 800000 in
private lemma step_emittedOperations_monotone
    (system : BlockSynchroniserSystem) (s : BelugaState) :
    ∀ op ∈ s.emittedOperations, op ∈ (step system s).emittedOperations := by
  intro op hop
  unfold step
  cases h : List.findSome? (fun x => tryActFor system s x.1 x.2) s.validators
  · simp; exact hop
  · simp only
    rw [List.findSome?_eq_some_iff] at h
    obtain ⟨l₁, a, l₂, h₁, h₂, _⟩ := h
    unfold tryActFor at h₂
    cases hb : List.find? (fun B => !hasAcceptedDigest s a.1 B.d &&
        B.parents.all fun pd => hasAcceptedDigest s a.1 pd) s.blocks <;>
      simp_all +decide
    · cases hb' : List.find? (fun B => hasAcceptedDigest s a.1 B.d &&
          !hasStoredDigest s a.1 B.d) s.blocks <;> simp_all +decide
      · split_ifs at h₂ <;>
          simp_all +decide [doPropose, doAdvance, updateValidator]
        all_goals subst h₂ ; grind
      · split_ifs at h₂ <;>
          simp_all +decide [doPropose, doStore, updateValidator]
        all_goals subst h₂ ; grind
    · split_ifs at h₂ <;>
        simp_all +decide [doPropose, doAccept, updateValidator]
      all_goals subst h₂ ; grind

/-- `hasProposedFor` is monotone in trace step: once it's true at some
step, it remains true at all later steps. -/
private lemma hasProposedFor_monotone
    (system : BlockSynchroniserSystem) (vid : ValidatorId) (r : Round)
    (i j : Nat) (hij : i ≤ j)
    (h : hasProposedFor (belugaTrace system i) vid r = true) :
    hasProposedFor (belugaTrace system j) vid r = true := by
  induction' hij with j _ ih
  · exact h
  · -- step j → step (j+1) preserves the propose op via emittedOperations monotonicity.
    unfold hasProposedFor at ih ⊢
    rw [List.any_eq_true] at ih ⊢
    obtain ⟨op, hop_mem, hop_match⟩ := ih
    refine ⟨op, ?_, hop_match⟩
    exact step_emittedOperations_monotone system _ op hop_mem

/- `updateValidator` preserves the list of validator IDs. -/
private lemma updateValidator_validators_ids_preserved (s : BelugaState)
    (vid : ValidatorId) (f : BelugaValidator → BelugaValidator) :
    (updateValidator s vid f).validators.map Prod.fst =
      s.validators.map Prod.fst := by
  unfold updateValidator
  simp only [List.map_map]
  apply List.map_congr_left
  rintro ⟨v, bv⟩ _
  by_cases h : v = vid <;> simp [h]

/-
`step` preserves the list of validator IDs. Each `tryActFor` branch
either leaves `s.validators` untouched (`doPropose`) or applies
`updateValidator` (preserves IDs).
-/
set_option maxHeartbeats 800000 in
private lemma step_validators_ids_preserved
    (system : BlockSynchroniserSystem) (s : BelugaState) :
    (step system s).validators.map Prod.fst = s.validators.map Prod.fst := by
  unfold step
  cases h_fs : List.findSome? (fun x => tryActFor system s x.1 x.2) s.validators with
  | none => simp
  | some s_post =>
    simp only
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, a, _, _, h_act, _⟩ := h_fs
    unfold tryActFor at h_act
    simp only at h_act
    rcases h_findAcc : List.find?
        (fun B => !hasAcceptedDigest s a.1 B.d &&
          B.parents.all fun pd => hasAcceptedDigest s a.1 pd) s.blocks
      with _ | B_acc
    · rw [h_findAcc] at h_act
      simp only at h_act
      rcases h_findSto : List.find?
          (fun B => hasAcceptedDigest s a.1 B.d &&
            !hasStoredDigest s a.1 B.d) s.blocks
        with _ | B_sto
      · rw [h_findSto] at h_act
        simp only at h_act
        by_cases h_prop : (!hasProposedFor s a.1 a.2.currentRound) = true
        · rw [if_pos h_prop] at h_act
          have : s_post = doPropose system s a.1 a.2.currentRound :=
            (Option.some.inj h_act).symm
          rw [this]
          unfold doPropose
          rfl
        · rw [if_neg h_prop] at h_act
          by_cases h_all : allProposedFor system s a.2.currentRound = true
          · rw [if_pos h_all] at h_act
            have : s_post = doAdvance s a.1 := (Option.some.inj h_act).symm
            rw [this, doAdvance]
            exact updateValidator_validators_ids_preserved s a.1 _
          · rw [if_neg h_all] at h_act
            simp at h_act
      · rw [h_findSto] at h_act
        simp only at h_act
        by_cases h_prop : (!hasProposedFor s a.1 a.2.currentRound) = true
        · rw [if_pos h_prop] at h_act
          have : s_post = doPropose system s a.1 a.2.currentRound :=
            (Option.some.inj h_act).symm
          rw [this]; unfold doPropose; rfl
        · rw [if_neg h_prop] at h_act
          have : s_post = doStore s a.1 B_sto := (Option.some.inj h_act).symm
          rw [this, doStore]
          exact updateValidator_validators_ids_preserved _ _ _
    · rw [h_findAcc] at h_act
      simp only at h_act
      by_cases h_prop : (!hasProposedFor s a.1 a.2.currentRound) = true
      · rw [if_pos h_prop] at h_act
        have : s_post = doPropose system s a.1 a.2.currentRound :=
          (Option.some.inj h_act).symm
        rw [this]; unfold doPropose; rfl
      · rw [if_neg h_prop] at h_act
        have : s_post = doAccept s a.1 B_acc := (Option.some.inj h_act).symm
        rw [this, doAccept]
        exact updateValidator_validators_ids_preserved _ _ _

/-
The Beluga trace preserves nodup-by-id of the validator list.
Foundation for `step_advance_implies_hasProposedFor`'s actor-vs-find
identification. Self-inductive (no other invariants required).
-/
private lemma belugaTrace_validators_nodup
    (system : BlockSynchroniserSystem)
    (h_sys_nodup : ValidatorsNodup system) (k : Nat) :
    ((belugaTrace system k).validators.map Prod.fst).Nodup := by
  induction k with
  | zero =>
    show ((BelugaState.init system).validators.map Prod.fst).Nodup
    unfold BelugaState.init
    simp [List.map_map]
    convert h_sys_nodup
  | succ k ih =>
    show ((step system (belugaTrace system k)).validators.map Prod.fst).Nodup
    rw [step_validators_ids_preserved]
    exact ih

/- Under nodup-by-id, `getValidator vid = some bv` iff `(vid, bv)` is in
the validators list. -/
private lemma getValidator_of_mem (s : BelugaState) (vid : ValidatorId)
    (bv : BelugaValidator) (h_nodup : (s.validators.map Prod.fst).Nodup)
    (h_mem : (vid, bv) ∈ s.validators) :
    s.getValidator vid = some bv := by
  unfold BelugaState.getValidator
  suffices h : s.validators.find? (fun x => x.1 == vid) = some (vid, bv) by
    rw [h]; rfl
  have aux : ∀ l : List (ValidatorId × BelugaValidator),
      (l.map Prod.fst).Nodup → (vid, bv) ∈ l →
      l.find? (fun x => x.1 == vid) = some (vid, bv) := by
    intro l
    induction l with
    | nil => intros _ h_mem; simp at h_mem
    | cons hd tl ih =>
      intros h_nodup h_mem
      rw [List.find?_cons]
      cases h_match : hd.1 == vid with
      | false =>
        rw [List.mem_cons] at h_mem
        rcases h_mem with h_eq | h_in
        · exfalso
          have h_hd_eq : hd.1 = vid := by rw [← h_eq]
          simp [h_hd_eq] at h_match
        · rw [List.map_cons] at h_nodup
          exact ih h_nodup.of_cons h_in
      | true =>
        rw [List.mem_cons] at h_mem
        rcases h_mem with h_eq | h_in
        · exact congrArg some h_eq.symm
        · exfalso
          rw [List.map_cons] at h_nodup
          have h_hd_eq : hd.1 = vid := by simpa using h_match
          apply h_nodup.notMem
          rw [h_hd_eq]
          exact List.mem_map.mpr ⟨(vid, bv), h_in, rfl⟩
  exact aux s.validators h_nodup h_mem

/- Under nodup-by-id, `s.getValidator vid = some bv` and a membership
record `(vid, bv') ∈ s.validators` force `bv = bv'`. -/
private lemma validator_value_unique
    (s : BelugaState) (vid : ValidatorId) (bv bv' : BelugaValidator)
    (h_nodup : (s.validators.map Prod.fst).Nodup)
    (h_get : s.getValidator vid = some bv)
    (h_mem : (vid, bv') ∈ s.validators) :
    bv = bv' := by
  have h_get' := getValidator_of_mem s vid bv' h_nodup h_mem
  rw [h_get] at h_get'
  exact Option.some.inj h_get'

/-
Inversion lemma for an advance step. If `vid`'s `currentRound`
advances by 1 in a single `step` (from `bv` at `s` to `bv'` at
`step system s`), then four things hold at `s`:
1. **propose-before-advance**: vid has proposed for its current round.
2. **accept-disabled**: every block in `s.blocks` is either accepted
   by vid, or has at least one parent vid hasn't accepted.
3. **store-disabled**: every block in `s.blocks` whose digest vid has
   accepted has been stored by vid.
4. **allProposedFor**: every registered validator has proposed for
   vid's current round.
Requires nodup-by-id of `s.validators` to identify the `findSome?`
actor with the `find?`-target.
-/
set_option maxHeartbeats 800000 in
private lemma step_advance_inversion
    (system : BlockSynchroniserSystem) (s : BelugaState) (vid : ValidatorId)
    (bv bv' : BelugaValidator)
    (h_nodup : (s.validators.map Prod.fst).Nodup)
    (h : s.getValidator vid = some bv)
    (h' : (step system s).getValidator vid = some bv')
    (h_advance : bv'.currentRound = bv.currentRound + 1) :
    hasProposedFor s vid bv.currentRound = true ∧
    (∀ B ∈ s.blocks,
      hasAcceptedDigest s vid B.d = true ∨
      ∃ pd ∈ B.parents, hasAcceptedDigest s vid pd = false) ∧
    (∀ B ∈ s.blocks,
      hasAcceptedDigest s vid B.d = true → hasStoredDigest s vid B.d = true) ∧
    allProposedFor system s bv.currentRound = true := by
  unfold step at h'
  rcases h_fs : List.findSome? (fun x => tryActFor system s x.1 x.2) s.validators
    with _ | s_post
  · rw [h_fs] at h'
    simp only at h'
    rw [h] at h'
    have h_eq : bv = bv' := Option.some.inj h'
    exfalso
    have : bv.currentRound = bv'.currentRound := by rw [h_eq]
    grind
  · rw [h_fs] at h'
    simp only at h'
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, a, _, h_split, h_act, _⟩ := h_fs
    have h_a_mem : a ∈ s.validators := by rw [h_split]; simp +decide
    unfold tryActFor at h_act
    simp only at h_act
    rcases h_findAcc : List.find?
        (fun B => !hasAcceptedDigest s a.1 B.d &&
          B.parents.all fun pd => hasAcceptedDigest s a.1 pd) s.blocks
      with _ | B_acc
    · rw [h_findAcc] at h_act
      simp only at h_act
      rcases h_findSto : List.find?
          (fun B => hasAcceptedDigest s a.1 B.d &&
            !hasStoredDigest s a.1 B.d) s.blocks
        with _ | B_sto
      · rw [h_findSto] at h_act
        simp only at h_act
        by_cases h_prop_gate : (!hasProposedFor s a.1 a.2.currentRound) = true
        · rw [if_pos h_prop_gate] at h_act
          have h_post_eq : s_post = doPropose system s a.1 a.2.currentRound :=
            (Option.some.inj h_act).symm
          rw [h_post_eq] at h'
          rw [doPropose_getValidator system s vid a.1 a.2.currentRound] at h'
          rw [h] at h'
          have h_eq : bv = bv' := Option.some.inj h'
          exfalso
          have : bv.currentRound = bv'.currentRound := by rw [h_eq]
          grind
        · rw [if_neg h_prop_gate] at h_act
          by_cases h_all : allProposedFor system s a.2.currentRound = true
          · rw [if_pos h_all] at h_act
            have h_post_eq : s_post = doAdvance s a.1 :=
              (Option.some.inj h_act).symm
            rw [h_post_eq] at h'
            have h_hpr : hasProposedFor s a.1 a.2.currentRound = true := by
              cases h_b : hasProposedFor s a.1 a.2.currentRound
              · exfalso; apply h_prop_gate; simp [h_b]
              · rfl
            by_cases h_eq_vid : vid = a.1
            · have h_a_pair_mem : (vid, a.2) ∈ s.validators := by
                have h_a_eq : a = (a.1, a.2) := by rfl
                grind
              have h_bv_eq_a2 : bv = a.2 :=
                validator_value_unique s vid bv a.2 h_nodup h h_a_pair_mem
              refine ⟨?_, ?_, ?_, ?_⟩
              · rw [h_eq_vid, h_bv_eq_a2]; exact h_hpr
              · intro B hB
                rw [List.find?_eq_none] at h_findAcc
                have h_no := h_findAcc B hB
                rw [h_eq_vid]
                by_cases h_acc : hasAcceptedDigest s a.1 B.d = true
                · left; exact h_acc
                · right
                  have h_acc_false : hasAcceptedDigest s a.1 B.d = false := by
                    cases h_b : hasAcceptedDigest s a.1 B.d
                    · rfl
                    · exact absurd h_b h_acc
                  have h_parents_false :
                      (B.parents.all (fun pd => hasAcceptedDigest s a.1 pd)) = false := by
                    rw [h_acc_false] at h_no
                    simpa using h_no
                  rw [List.all_eq_false] at h_parents_false
                  obtain ⟨pd, h_pd_mem, h_pd_neq⟩ := h_parents_false
                  refine ⟨pd, h_pd_mem, ?_⟩
                  cases h_b : hasAcceptedDigest s a.1 pd
                  · rfl
                  · exact absurd h_b h_pd_neq
              · intro B hB h_acc
                rw [h_eq_vid] at h_acc
                rw [List.find?_eq_none] at h_findSto
                have h_no := h_findSto B hB
                rw [h_eq_vid]
                by_cases h_sto : hasStoredDigest s a.1 B.d = true
                · exact h_sto
                · exfalso
                  have h_sto_false : hasStoredDigest s a.1 B.d = false := by
                    cases h_b : hasStoredDigest s a.1 B.d
                    · rfl
                    · exact absurd h_b h_sto
                  rw [h_acc, h_sto_false] at h_no
                  simp at h_no
              · rw [h_bv_eq_a2]; exact h_all
            · rw [doAdvance] at h'
              rw [updateValidator_getValidator_ne s vid a.1 _ h_eq_vid] at h'
              rw [h] at h'
              have h_eq : bv = bv' := Option.some.inj h'
              exfalso
              have : bv.currentRound = bv'.currentRound := by rw [h_eq]
              grind
          · rw [if_neg h_all] at h_act
            simp at h_act
      · rw [h_findSto] at h_act
        simp only at h_act
        by_cases h_prop_gate : (!hasProposedFor s a.1 a.2.currentRound) = true
        · rw [if_pos h_prop_gate] at h_act
          have h_post_eq : s_post = doPropose system s a.1 a.2.currentRound :=
            (Option.some.inj h_act).symm
          rw [h_post_eq] at h'
          rw [doPropose_getValidator system s vid a.1 a.2.currentRound] at h'
          rw [h] at h'
          have h_eq : bv = bv' := Option.some.inj h'
          exfalso
          have : bv.currentRound = bv'.currentRound := by rw [h_eq]
          grind
        · rw [if_neg h_prop_gate] at h_act
          have h_post_eq : s_post = doStore s a.1 B_sto :=
            (Option.some.inj h_act).symm
          rw [h_post_eq] at h'
          obtain ⟨bv_post, h_post_get, h_eq_round⟩ := doStore_round s vid a.1 B_sto bv h
          have h_eq : bv_post = bv' := Option.some.inj (h_post_get.symm.trans h')
          subst h_eq
          grind
    · rw [h_findAcc] at h_act
      simp only at h_act
      by_cases h_prop_gate : (!hasProposedFor s a.1 a.2.currentRound) = true
      · rw [if_pos h_prop_gate] at h_act
        have h_post_eq : s_post = doPropose system s a.1 a.2.currentRound :=
          (Option.some.inj h_act).symm
        rw [h_post_eq] at h'
        rw [doPropose_getValidator system s vid a.1 a.2.currentRound] at h'
        rw [h] at h'
        have h_eq : bv = bv' := Option.some.inj h'
        exfalso
        have : bv.currentRound = bv'.currentRound := by rw [h_eq]
        grind
      · rw [if_neg h_prop_gate] at h_act
        have h_post_eq : s_post = doAccept s a.1 B_acc :=
          (Option.some.inj h_act).symm
        rw [h_post_eq] at h'
        obtain ⟨bv_post, h_post_get, h_eq_round⟩ := doAccept_round s vid a.1 B_acc bv h
        have h_eq : bv_post = bv' := Option.some.inj (h_post_get.symm.trans h')
        subst h_eq
        grind

/- Projection of `step_advance_inversion`: propose-before-advance. -/
private lemma step_advance_implies_hasProposedFor
    (system : BlockSynchroniserSystem) (s : BelugaState) (vid : ValidatorId)
    (bv bv' : BelugaValidator)
    (h_nodup : (s.validators.map Prod.fst).Nodup)
    (h : s.getValidator vid = some bv)
    (h' : (step system s).getValidator vid = some bv')
    (h_advance : bv'.currentRound = bv.currentRound + 1) :
    hasProposedFor s vid bv.currentRound = true :=
  (step_advance_inversion system s vid bv bv' h_nodup h h' h_advance).1

/- Projection of `step_advance_inversion`: store-disabled. -/
private lemma step_advance_implies_stored
    (system : BlockSynchroniserSystem) (s : BelugaState) (vid : ValidatorId)
    (bv bv' : BelugaValidator)
    (h_nodup : (s.validators.map Prod.fst).Nodup)
    (h : s.getValidator vid = some bv)
    (h' : (step system s).getValidator vid = some bv')
    (h_advance : bv'.currentRound = bv.currentRound + 1) :
    ∀ B ∈ s.blocks,
      hasAcceptedDigest s vid B.d = true → hasStoredDigest s vid B.d = true :=
  (step_advance_inversion system s vid bv bv' h_nodup h h' h_advance).2.2.1

/- Projection of `step_advance_inversion`: accept-disabled. -/
private lemma step_advance_implies_acceptComplete
    (system : BlockSynchroniserSystem) (s : BelugaState) (vid : ValidatorId)
    (bv bv' : BelugaValidator)
    (h_nodup : (s.validators.map Prod.fst).Nodup)
    (h : s.getValidator vid = some bv)
    (h' : (step system s).getValidator vid = some bv')
    (h_advance : bv'.currentRound = bv.currentRound + 1) :
    ∀ B ∈ s.blocks,
      hasAcceptedDigest s vid B.d = true ∨
      ∃ pd ∈ B.parents, hasAcceptedDigest s vid pd = false :=
  (step_advance_inversion system s vid bv bv' h_nodup h h' h_advance).2.1

/- Projection of `step_advance_inversion`: allProposedFor gate. -/
private lemma step_advance_implies_allProposedFor
    (system : BlockSynchroniserSystem) (s : BelugaState) (vid : ValidatorId)
    (bv bv' : BelugaValidator)
    (h_nodup : (s.validators.map Prod.fst).Nodup)
    (h : s.getValidator vid = some bv)
    (h' : (step system s).getValidator vid = some bv')
    (h_advance : bv'.currentRound = bv.currentRound + 1) :
    allProposedFor system s bv.currentRound = true :=
  (step_advance_inversion system s vid bv bv' h_nodup h h' h_advance).2.2.2

/- `step` preserves "absent": if vid isn't in `s.validators`, it isn't
in `(step system s).validators` either. -/
private lemma step_preserves_none (system : BlockSynchroniserSystem)
    (s : BelugaState) (vid : ValidatorId)
    (h : s.getValidator vid = none) :
    (step system s).getValidator vid = none := by
  unfold BelugaState.getValidator at h ⊢
  rw [Option.map_eq_none_iff] at h ⊢
  rw [List.find?_eq_none] at h ⊢
  have h_keys := step_validators_ids_preserved system s
  intro x hx h_match
  have h_x_key : x.1 ∈ (step system s).validators.map Prod.fst :=
    List.mem_map.mpr ⟨x, hx, rfl⟩
  rw [h_keys] at h_x_key
  obtain ⟨y, hy_mem, hy_eq⟩ := List.mem_map.mp h_x_key
  apply h y hy_mem
  grind

/-
Trace invariant: at every step `k`, every validator `vid` with
`currentRound = R` has `hasProposedFor` true for every `r' < R`.
Self-inductive on `k`, using the propose-before-advance gate
extracted by `step_advance_implies_hasProposedFor`.
-/
private lemma proposed_for_lt_currentRound
    (system : BlockSynchroniserSystem)
    (h_sys_nodup : ValidatorsNodup system) :
    ∀ k vid bv, (belugaTrace system k).getValidator vid = some bv →
      ∀ r' < bv.currentRound, hasProposedFor (belugaTrace system k) vid r' = true := by
  intro k
  induction k with
  | zero =>
    intro vid bv h_get r' h_lt
    have h_round : bv.currentRound = 0 :=
      getValidator_init_round_zero system vid bv h_get
    rw [h_round] at h_lt
    exact absurd h_lt (Nat.not_lt_zero _)
  | succ k ih =>
    intro vid bv h_get r' h_lt
    have h_present_k : ∃ bv_prev, (belugaTrace system k).getValidator vid = some bv_prev := by
      by_contra h_none
      push_neg at h_none
      have h_get_none : (belugaTrace system k).getValidator vid = none :=
        Option.eq_none_iff_forall_ne_some.mpr h_none
      have h_succ_none : (belugaTrace system (k+1)).getValidator vid = none :=
        step_preserves_none system _ vid h_get_none
      rw [h_succ_none] at h_get
      contradiction
    obtain ⟨bv_prev, h_prev⟩ := h_present_k
    have h_mono : bv_prev.currentRound ≤ bv.currentRound :=
      step_round_monotone system _ vid bv_prev bv h_prev h_get
    have h_at_most_one : bv.currentRound ≤ bv_prev.currentRound + 1 :=
      step_round_at_most_one system _ vid bv_prev bv h_prev h_get
    by_cases h_eq : bv.currentRound = bv_prev.currentRound
    · -- Preserved: IH at k + monotone.
      rw [h_eq] at h_lt
      have h_prop_k := ih vid bv_prev h_prev r' h_lt
      exact hasProposedFor_monotone system vid r' k (k+1) (Nat.le_succ k) h_prop_k
    · -- Advanced: bv.currentRound = bv_prev.currentRound + 1.
      have h_advance : bv.currentRound = bv_prev.currentRound + 1 := by grind
      by_cases h_lt' : r' < bv_prev.currentRound
      · -- IH + monotone.
        have h_prop_k := ih vid bv_prev h_prev r' h_lt'
        exact hasProposedFor_monotone system vid r' k (k+1) (Nat.le_succ k) h_prop_k
      · -- r' = bv_prev.currentRound. Use the advance-implies-hasProposedFor gate.
        have h_eq_r : r' = bv_prev.currentRound := by grind
        rw [h_eq_r]
        have h_nodup_k := belugaTrace_validators_nodup system h_sys_nodup k
        have h_prop_k :=
          step_advance_implies_hasProposedFor system _ vid bv_prev bv
            h_nodup_k h_prev h_get h_advance
        exact hasProposedFor_monotone system vid bv_prev.currentRound k (k+1)
          (Nat.le_succ k) h_prop_k

/- Find the step at which `vid` first advances from round `r` to `r + 1`,
given a starting step at round `r` and an ending step at round ≥ `r + 1`.
The witness step `k_a` satisfies `bv at trace k_a = r` and
`bv' at trace (k_a + 1) = r + 1`. -/
private lemma find_advance_step
    (system : BlockSynchroniserSystem) (vid : ValidatorId) (r : Round) :
    ∀ {k₀ k_target}, k₀ ≤ k_target →
    ∀ bv₀ bv_t,
    (belugaTrace system k₀).getValidator vid = some bv₀ →
    (belugaTrace system k_target).getValidator vid = some bv_t →
    bv₀.currentRound = r →
    bv_t.currentRound ≥ r + 1 →
    ∃ k_a bv bv',
      k₀ ≤ k_a ∧ k_a < k_target ∧
      (belugaTrace system k_a).getValidator vid = some bv ∧
      (belugaTrace system (k_a + 1)).getValidator vid = some bv' ∧
      bv.currentRound = r ∧ bv'.currentRound = r + 1 := by
  intros k₀ k_target hle
  induction hle with
  | refl =>
    intros bv₀ bv_t h₀ h_t hr₀ hr_t
    rw [h₀] at h_t
    have h_eq : bv₀ = bv_t := Option.some.inj h_t
    exfalso
    have h_round_eq : bv₀.currentRound = bv_t.currentRound := by rw [h_eq]
    grind
  | @step k_target' h ih =>
    intros bv₀ bv_t h₀ h_t hr₀ hr_t
    have h_persistent_prev :
        ∃ bv_prev, (belugaTrace system k_target').getValidator vid = some bv_prev := by
      by_contra h_none
      push_neg at h_none
      have h_get_none : (belugaTrace system k_target').getValidator vid = none :=
        Option.eq_none_iff_forall_ne_some.mpr h_none
      have h_succ_none : (belugaTrace system (k_target' + 1)).getValidator vid = none :=
        step_preserves_none system _ vid h_get_none
      rw [h_succ_none] at h_t
      contradiction
    obtain ⟨bv_prev, h_prev⟩ := h_persistent_prev
    have h_step_at_most : bv_t.currentRound ≤ bv_prev.currentRound + 1 :=
      step_round_at_most_one system _ vid bv_prev bv_t h_prev h_t
    by_cases h_case : bv_prev.currentRound ≥ r + 1
    · obtain ⟨k_a, bv_a, bv_a', h_le, h_lt, h_a, h_a', h_eq_r, h_eq_r1⟩ :=
        ih bv₀ bv_prev h₀ h_prev hr₀ h_case
      exact ⟨k_a, bv_a, bv_a', h_le, Nat.lt_succ_of_lt h_lt, h_a, h_a', h_eq_r, h_eq_r1⟩
    · push_neg at h_case
      have hbp_le_r : bv_prev.currentRound ≤ r := Nat.le_of_lt_succ h_case
      have hbp_ge_r : bv_prev.currentRound ≥ r := by
        have : r + 1 ≤ bv_prev.currentRound + 1 := le_trans hr_t h_step_at_most
        exact Nat.le_of_succ_le_succ this
      have hbp_eq : bv_prev.currentRound = r := le_antisymm hbp_le_r hbp_ge_r
      have hbt_eq : bv_t.currentRound = r + 1 := by
        have h1 : bv_t.currentRound ≤ r + 1 := by rw [← hbp_eq] at hr_t ⊢; exact h_step_at_most
        exact le_antisymm h1 hr_t
      exact ⟨k_target', bv_prev, bv_t, h, Nat.lt_succ_self _, h_prev, h_t, hbp_eq, hbt_eq⟩

/- Trace invariant: every block in the pool has all its parent digests
corresponding to round-`(B.r - 1)` blocks in the pool. (For round-0
blocks, this implicitly forces `B.parents = []` since no block has
round `-1`.) By construction: `doPropose` constructs parents as
digests of all round-`(r-1)` blocks in `s.blocks` at propose time
(empty for `r = 0`), and other actions preserve `s.blocks`. -/
set_option maxHeartbeats 800000 in
private lemma block_parents_in_pool
    (system : BlockSynchroniserSystem) (k : Nat) :
    ∀ B ∈ (belugaTrace system k).blocks, ∀ pd ∈ B.parents,
      ∃ B_p ∈ (belugaTrace system k).blocks, B_p.d = pd ∧ B_p.r + 1 = B.r := by
  induction k with
  | zero =>
    intro B hB
    cases hB
  | succ k ih =>
    intro B hB pd hpd
    show ∃ B_p ∈ (step system (belugaTrace system k)).blocks, B_p.d = pd ∧ B_p.r + 1 = B.r
    set s := belugaTrace system k with h_s_def
    show ∃ B_p ∈ (step system s).blocks, B_p.d = pd ∧ B_p.r + 1 = B.r
    have h_blocks_mono : ∀ B', B' ∈ s.blocks → B' ∈ (step system s).blocks := by
      intro B' hB'
      unfold step
      cases h_fs : List.findSome? (fun x => tryActFor system s x.1 x.2) s.validators with
      | none => simp; exact hB'
      | some s_post =>
        simp only
        rw [List.findSome?_eq_some_iff] at h_fs
        obtain ⟨_, a, _, _, h_act, _⟩ := h_fs
        unfold tryActFor at h_act
        simp only at h_act
        rcases h_findAcc : List.find?
            (fun B => !hasAcceptedDigest s a.1 B.d &&
              B.parents.all fun pd => hasAcceptedDigest s a.1 pd) s.blocks
          with _ | B_acc
        · rw [h_findAcc] at h_act
          simp only at h_act
          rcases h_findSto : List.find?
              (fun B => hasAcceptedDigest s a.1 B.d &&
                !hasStoredDigest s a.1 B.d) s.blocks
            with _ | B_sto
          · rw [h_findSto] at h_act
            simp only at h_act
            by_cases h_p : (!hasProposedFor s a.1 a.2.currentRound) = true
            · rw [if_pos h_p] at h_act
              have : s_post = doPropose system s a.1 a.2.currentRound :=
                (Option.some.inj h_act).symm
              rw [this]; exact doPropose_blocks system s _ _ _ hB'
            · rw [if_neg h_p] at h_act
              by_cases h_a : allProposedFor system s a.2.currentRound = true
              · rw [if_pos h_a] at h_act
                have : s_post = doAdvance s a.1 := (Option.some.inj h_act).symm
                rw [this, doAdvance_blocks_eq]; exact hB'
              · rw [if_neg h_a] at h_act; simp at h_act
          · rw [h_findSto] at h_act
            simp only at h_act
            by_cases h_p : (!hasProposedFor s a.1 a.2.currentRound) = true
            · rw [if_pos h_p] at h_act
              have : s_post = doPropose system s a.1 a.2.currentRound :=
                (Option.some.inj h_act).symm
              rw [this]; exact doPropose_blocks system s _ _ _ hB'
            · rw [if_neg h_p] at h_act
              have : s_post = doStore s a.1 B_sto := (Option.some.inj h_act).symm
              rw [this, doStore_blocks_eq]; exact hB'
        · rw [h_findAcc] at h_act
          simp only at h_act
          by_cases h_p : (!hasProposedFor s a.1 a.2.currentRound) = true
          · rw [if_pos h_p] at h_act
            have : s_post = doPropose system s a.1 a.2.currentRound :=
              (Option.some.inj h_act).symm
            rw [this]; exact doPropose_blocks system s _ _ _ hB'
          · rw [if_neg h_p] at h_act
            have : s_post = doAccept s a.1 B_acc := (Option.some.inj h_act).symm
            rw [this, doAccept_blocks_eq]; exact hB'
    show ∃ B_p ∈ (step system s).blocks, B_p.d = pd ∧ B_p.r + 1 = B.r
    change B ∈ (step system s).blocks at hB
    unfold step at hB
    cases h_fs : List.findSome? (fun x => tryActFor system s x.1 x.2) s.validators with
    | none =>
      rw [h_fs] at hB; simp only at hB
      obtain ⟨B_p, hB_p, hd, hr_p⟩ := ih B hB pd hpd
      exact ⟨B_p, h_blocks_mono B_p hB_p, hd, hr_p⟩
    | some s_post =>
      rw [h_fs] at hB
      simp only at hB
      rw [List.findSome?_eq_some_iff] at h_fs
      obtain ⟨_, a, _, _, h_act, _⟩ := h_fs
      unfold tryActFor at h_act
      simp only at h_act
      rcases h_findAcc : List.find?
          (fun B => !hasAcceptedDigest s a.1 B.d &&
            B.parents.all fun pd => hasAcceptedDigest s a.1 pd) s.blocks
        with _ | B_acc
      · rw [h_findAcc] at h_act
        simp only at h_act
        rcases h_findSto : List.find?
            (fun B => hasAcceptedDigest s a.1 B.d &&
              !hasStoredDigest s a.1 B.d) s.blocks
          with _ | B_sto
        · rw [h_findSto] at h_act
          simp only at h_act
          by_cases h_p : (!hasProposedFor s a.1 a.2.currentRound) = true
          · -- doPropose case: B is either old or = newB.
            rw [if_pos h_p] at h_act
            have h_post : s_post = doPropose system s a.1 a.2.currentRound :=
              (Option.some.inj h_act).symm
            rw [h_post] at hB
            unfold doPropose at hB
            simp only at hB
            rw [List.mem_cons] at hB
            rcases hB with h_eq | hB_old
            · subst h_eq
              by_cases hzero : a.2.currentRound = 0
              · rw [hzero] at hpd; simp at hpd
              · simp only [if_neg hzero] at hpd
                rw [List.mem_map] at hpd
                obtain ⟨B_p, hB_p_mem, hB_p_d⟩ := hpd
                rw [List.mem_filter] at hB_p_mem
                obtain ⟨hB_p_in, hB_p_round⟩ := hB_p_mem
                refine ⟨B_p, h_blocks_mono B_p hB_p_in, hB_p_d, ?_⟩
                show B_p.r + 1 = a.2.currentRound
                have h1 : B_p.r = a.2.currentRound - 1 := by simpa using hB_p_round
                have h_ne : a.2.currentRound ≠ 0 := hzero
                rw [h1]
                exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h_ne)
            · -- B is old.
              obtain ⟨B_p, hB_p_mem, hd_eq, hr_eq⟩ := ih B hB_old pd hpd
              refine ⟨B_p, h_blocks_mono B_p hB_p_mem, hd_eq, hr_eq⟩
          · -- doAdvance case: blocks unchanged.
            rw [if_neg h_p] at h_act
            by_cases h_a : allProposedFor system s a.2.currentRound = true
            · rw [if_pos h_a] at h_act
              have h_post : s_post = doAdvance s a.1 := (Option.some.inj h_act).symm
              rw [h_post, doAdvance_blocks_eq] at hB
              obtain ⟨B_p, hB_p, hd, hr_p⟩ := ih B hB pd hpd
              exact ⟨B_p, h_blocks_mono B_p hB_p, hd, hr_p⟩
            · rw [if_neg h_a] at h_act; simp at h_act
        · rw [h_findSto] at h_act
          simp only at h_act
          by_cases h_p : (!hasProposedFor s a.1 a.2.currentRound) = true
          · rw [if_pos h_p] at h_act
            have h_post : s_post = doPropose system s a.1 a.2.currentRound :=
              (Option.some.inj h_act).symm
            rw [h_post] at hB
            unfold doPropose at hB
            simp only at hB
            rw [List.mem_cons] at hB
            rcases hB with h_eq | hB_old
            · subst h_eq
              by_cases hzero : a.2.currentRound = 0
              · rw [hzero] at hpd; simp at hpd
              · simp only [if_neg hzero] at hpd
                rw [List.mem_map] at hpd
                obtain ⟨B_p, hB_p_mem, hB_p_d⟩ := hpd
                rw [List.mem_filter] at hB_p_mem
                obtain ⟨hB_p_in, hB_p_round⟩ := hB_p_mem
                refine ⟨B_p, h_blocks_mono B_p hB_p_in, hB_p_d, ?_⟩
                show B_p.r + 1 = a.2.currentRound
                have h1 : B_p.r = a.2.currentRound - 1 := by simpa using hB_p_round
                have h_ne : a.2.currentRound ≠ 0 := hzero
                rw [h1]
                exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h_ne)
            · obtain ⟨B_p, hB_p_mem, hd_eq, hr_eq⟩ := ih B hB_old pd hpd
              refine ⟨B_p, h_blocks_mono B_p hB_p_mem, hd_eq, hr_eq⟩
          · rw [if_neg h_p] at h_act
            have h_post : s_post = doStore s a.1 B_sto := (Option.some.inj h_act).symm
            rw [h_post, doStore_blocks_eq] at hB
            obtain ⟨B_p, hB_p, hd, hr_p⟩ := ih B hB pd hpd
            exact ⟨B_p, h_blocks_mono B_p hB_p, hd, hr_p⟩
      · rw [h_findAcc] at h_act
        simp only at h_act
        by_cases h_p : (!hasProposedFor s a.1 a.2.currentRound) = true
        · rw [if_pos h_p] at h_act
          have h_post : s_post = doPropose system s a.1 a.2.currentRound :=
            (Option.some.inj h_act).symm
          rw [h_post] at hB
          unfold doPropose at hB
          simp only at hB
          rw [List.mem_cons] at hB
          rcases hB with h_eq | hB_old
          · subst h_eq
            by_cases hzero : a.2.currentRound = 0
            · rw [hzero] at hpd; simp at hpd
            · simp only [if_neg hzero] at hpd
              rw [List.mem_map] at hpd
              obtain ⟨B_p, hB_p_mem, hB_p_d⟩ := hpd
              rw [List.mem_filter] at hB_p_mem
              obtain ⟨hB_p_in, hB_p_round⟩ := hB_p_mem
              refine ⟨B_p, h_blocks_mono B_p hB_p_in, hB_p_d, ?_⟩
              show B_p.r + 1 = a.2.currentRound
              have h1 : B_p.r = a.2.currentRound - 1 := by simpa using hB_p_round
              have h_ne : a.2.currentRound ≠ 0 := hzero
              rw [h1]
              exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h_ne)
          · obtain ⟨B_p, hB_p_mem, hd_eq, hr_eq⟩ := ih B hB_old pd hpd
            refine ⟨B_p, h_blocks_mono B_p hB_p_mem, hd_eq, hr_eq⟩
        · rw [if_neg h_p] at h_act
          have h_post : s_post = doAccept s a.1 B_acc := (Option.some.inj h_act).symm
          rw [h_post, doAccept_blocks_eq] at hB
          obtain ⟨B_p, hB_p, hd, hr_p⟩ := ih B hB pd hpd
          exact ⟨B_p, h_blocks_mono B_p hB_p, hd, hr_p⟩

/- At an advance step (vid at round `R` at trace `k_a`, at round
`R + 1` at trace `(k_a + 1)`), vid has accepted every block in
`(trace k_a).blocks` of round ≤ `R`. Proof by strong induction on
`B.r`: accept-disabled at the advance step gives "accepted ∨ ∃
unaccepted parent"; `block_parents_in_pool` produces a round-`(B.r-1)`
block in pool for each parent digest, and the IH gives vid has
accepted that block's digest. -/
private lemma accepted_at_advance
    (system : BlockSynchroniserSystem)
    (h_sys_nodup : ValidatorsNodup system)
    (k_a R : Nat) (vid : ValidatorId) (bv bv' : BelugaValidator)
    (h_a : (belugaTrace system k_a).getValidator vid = some bv)
    (h_a' : (belugaTrace system (k_a + 1)).getValidator vid = some bv')
    (h_R : bv.currentRound = R)
    (h_advance : bv'.currentRound = R + 1) :
    ∀ B ∈ (belugaTrace system k_a).blocks, B.r ≤ R →
      hasAcceptedDigest (belugaTrace system k_a) vid B.d = true := by
  have h_advance' : bv'.currentRound = bv.currentRound + 1 := by rw [h_R]; exact h_advance
  have h_nodup_a := belugaTrace_validators_nodup system h_sys_nodup k_a
  have h_acc_complete :=
    step_advance_implies_acceptComplete system _ vid bv bv' h_nodup_a h_a h_a' h_advance'
  suffices h : ∀ r, ∀ B ∈ (belugaTrace system k_a).blocks, B.r = r → r ≤ R →
      hasAcceptedDigest (belugaTrace system k_a) vid B.d = true by
    intro B hB hBR
    exact h B.r B hB rfl hBR
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro B hB hBeq hBR
    rcases h_acc_complete B hB with h_acc | ⟨pd, h_pd_mem, h_pd_unacc⟩
    · exact h_acc
    · exfalso
      obtain ⟨B_p, hB_p, hB_p_d, hB_p_r⟩ := block_parents_in_pool system k_a B hB pd h_pd_mem
      have h_lt : B_p.r < r := by
        rw [← hBeq, ← hB_p_r]
        exact Nat.lt_succ_self _
      have h_pR : B_p.r ≤ R := le_trans (Nat.le_of_lt h_lt) hBR
      have h_p_acc : hasAcceptedDigest (belugaTrace system k_a) vid B_p.d = true :=
        ih B_p.r h_lt B_p hB_p rfl h_pR
      rw [hB_p_d] at h_p_acc
      rw [h_p_acc] at h_pd_unacc
      cases h_pd_unacc

/-
Iterated `SchedulerFairness`: starting from a post-GST step, every
honest validator can be brought to currentRound ≥ R for any R, by
applying `h_fair` `R` times. Requires a witness honest validator
to drive the iteration.
-/
private lemma all_honest_eventually_at_round
    (system : BlockSynchroniserSystem)
    (time : TimeMap) (h_time : time.WellFormed)
    (h_fair : SchedulerFairness system time)
    (vid_w : ValidatorId) (h_w : isHonestValidator system vid_w = true)
    (k₀ : Nat) (h_gst : time k₀ ≥ system.GST) :
    ∀ R, ∃ k, k₀ ≤ k ∧ time k ≥ system.GST ∧
      ∀ vid, isHonestValidator system vid = true →
        ∃ bv, (belugaTrace system k).getValidator vid = some bv ∧
              bv.currentRound ≥ R := by
  intro R
  induction R with
  | zero =>
    refine ⟨k₀, le_refl _, h_gst, ?_⟩
    intro vid h_vid
    obtain ⟨bv, h_bv⟩ := honest_validator_persistent_trace system vid h_vid k₀
    exact ⟨bv, h_bv, Nat.zero_le _⟩
  | succ R ih =>
    obtain ⟨k_R, h_k_R_le, h_k_R_gst, h_all_R⟩ := ih
    obtain ⟨bv_w, h_bv_w, h_bv_w_round⟩ := h_all_R vid_w h_w
    obtain ⟨k', h_k'_le, _, h_all_succ⟩ :=
      h_fair k_R bv_w.currentRound h_k_R_gst ⟨vid_w, bv_w, h_w, h_bv_w, rfl⟩
    refine ⟨k', le_trans h_k_R_le h_k'_le,
      le_trans h_k_R_gst (h_time.1 _ _ h_k'_le), ?_⟩
    intro vid h_vid
    obtain ⟨bv', h_bv', h_bv'_round⟩ := h_all_succ vid h_vid
    exact ⟨bv', h_bv', le_trans (Nat.succ_le_succ h_bv_w_round) h_bv'_round⟩

/- `hasProposedFor s vid r = true` iff a `block_propose vid _ r` op
is in `s.emittedOperations`. Bridge between the boolean predicate
and the operation-list witness. -/
private lemma hasProposedFor_iff_mem (s : BelugaState)
    (vid : ValidatorId) (r : Round) :
    hasProposedFor s vid r = true ↔
    ∃ B, ValidatorOperation.block_propose vid B r ∈ s.emittedOperations := by
  unfold hasProposedFor
  rw [List.any_eq_true]
  constructor
  · rintro ⟨op, hop_mem, hop_match⟩
    cases op with
    | block_propose v B r' =>
      simp at hop_match
      obtain ⟨h_v, h_r⟩ := hop_match
      exact ⟨B, h_v ▸ h_r ▸ hop_mem⟩
    | _ => simp at hop_match
  · rintro ⟨B, h_mem⟩
    refine ⟨ValidatorOperation.block_propose vid B r, h_mem, ?_⟩
    simp +decide

/- Generic version of `getValidator_of_mem` for any `(α × β)` list with
nodup-by-fst. Used to identify the find?-result on `system.validators`
(which is `(ValidatorId × Bool)`) and on `BelugaState.validators`. -/
private lemma find_of_mem_nodup_fst {α β : Type*} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (a : α) (b : β)
    (h_nodup : (l.map Prod.fst).Nodup) (h_mem : (a, b) ∈ l) :
    l.find? (fun x => x.1 == a) = some (a, b) := by
  induction l with
  | nil => simp at h_mem
  | cons hd tl ih =>
    rw [List.find?_cons]
    cases h_match : hd.1 == a with
    | false =>
      rw [List.mem_cons] at h_mem
      rcases h_mem with h_eq | h_in
      · exfalso
        have : hd.1 = a := by rw [← h_eq]
        simp [this] at h_match
      · rw [List.map_cons] at h_nodup
        exact ih h_nodup.of_cons h_in
    | true =>
      rw [List.mem_cons] at h_mem
      rcases h_mem with h_eq | h_in
      · exact congrArg some h_eq.symm
      · exfalso
        rw [List.map_cons] at h_nodup
        have h_hd_eq : hd.1 = a := by simpa using h_match
        apply h_nodup.notMem
        rw [h_hd_eq]
        exact List.mem_map.mpr ⟨(a, b), h_in, rfl⟩

/- For a pair `(vid, true)` in `system.validators` with nodup-by-id,
`isHonestValidator system vid = true`. -/
private lemma isHonestValidator_of_mem
    (system : BlockSynchroniserSystem) (vid : ValidatorId)
    (h_nodup : ValidatorsNodup system)
    (h_mem : (vid, true) ∈ system.validators) :
    isHonestValidator system vid = true := by
  unfold isHonestValidator BlockSynchroniserSystem.isHonest
  have h_find : system.validators.find? (fun (id, _) => id == vid) = some (vid, true) :=
    find_of_mem_nodup_fst system.validators vid true h_nodup h_mem
  rw [← find_beq_eq_find, h_find]

/- T3 (paper §5): post-GST round-progression. For every round, there
is a step at which ≥ 2f+1 distinct honest validators have proposed
for that round. Iterates `SchedulerFairness` to bring all honest
validators past the target round, then extracts their propose ops
via `proposed_for_lt_currentRound` and counts via `toFinset.card`. -/
private lemma round_progression_aux
    (system : BlockSynchroniserSystem)
    (time : TimeMap) (h_time : time.WellFormed)
    (h_fair : SchedulerFairness system time)
    (hHonest : HonestBFTBound system)
    (h_sys_nodup : ValidatorsNodup system) :
    RoundProgression system (belugaTrace system) := by
  intro round
  unfold HonestBFTBound at hHonest
  set honest_pairs := system.validators.filter (fun p => p.2 = true) with h_hp_def
  have h_hp_ne : honest_pairs ≠ [] := by
    intro h_e
    rw [h_e] at hHonest
    simp at hHonest
  have h_pair_w_mem : honest_pairs.head h_hp_ne ∈ honest_pairs := List.head_mem _
  set pair_w := honest_pairs.head h_hp_ne with h_pw_def
  have h_pw_filter := List.mem_filter.mp h_pair_w_mem
  have h_pw_in : pair_w ∈ system.validators := h_pw_filter.1
  have h_pw_true : pair_w.2 = true := by simpa using h_pw_filter.2
  set vid_w := pair_w.1
  have h_w_pair_eq : (vid_w, true) ∈ system.validators := by
    have h_eq : pair_w = (vid_w, true) := by
      apply Prod.ext
      · rfl
      · exact h_pw_true
    rw [← h_eq]; exact h_pw_in
  have h_w_honest : isHonestValidator system vid_w = true :=
    isHonestValidator_of_mem system vid_w h_sys_nodup h_w_pair_eq
  obtain ⟨k₀, h_k₀_gst⟩ := h_time.2 system.GST
  obtain ⟨k, _, _, h_all⟩ :=
    all_honest_eventually_at_round system time h_time h_fair vid_w h_w_honest
      k₀ h_k₀_gst (round + 1)
  refine ⟨k, ?_⟩
  set honest_vids := honest_pairs.map Prod.fst with h_hv_def
  have h_hv_len : honest_vids.length ≥ 2 * system.f + 1 := by
    rw [h_hv_def, List.length_map]; exact hHonest
  have h_hp_nodup_records : honest_pairs.Nodup := by
    rw [h_hp_def]
    apply List.Nodup.filter
    exact List.Nodup.of_map _ h_sys_nodup
  have h_hv_nodup : honest_vids.Nodup := by
    rw [h_hv_def]
    apply List.Nodup.map_on _ h_hp_nodup_records
    intro x hx y hy h_eq
    have hx_in : x ∈ system.validators := (List.mem_filter.mp hx).1
    have hy_in : y ∈ system.validators := (List.mem_filter.mp hy).1
    have hx_find : system.validators.find? (fun z => z.1 == x.1) = some x :=
      find_of_mem_nodup_fst system.validators x.1 x.2 h_sys_nodup hx_in
    have hy_find : system.validators.find? (fun z => z.1 == y.1) = some y :=
      find_of_mem_nodup_fst system.validators y.1 y.2 h_sys_nodup hy_in
    rw [h_eq] at hx_find
    rw [hx_find] at hy_find
    grind
  set proposers_raw := (opsAt (belugaTrace system) k).filterMap (fun op =>
    match op with
    | .block_propose vid _ r => if r = round then some vid else none
    | _ => none) with h_pr_def
  have h_subset : ∀ vid ∈ honest_vids, vid ∈ proposers_raw := by
    intro vid h_vid_mem
    obtain ⟨pair, h_pair_mem, h_pair_fst⟩ := List.mem_map.mp h_vid_mem
    have h_pair_filter := List.mem_filter.mp h_pair_mem
    have h_pair_in : pair ∈ system.validators := h_pair_filter.1
    have h_pair_true : pair.2 = true := by simpa using h_pair_filter.2
    have h_vid_pair_in : (vid, true) ∈ system.validators := by
      have h_pair_eq : pair = (vid, true) := by
        apply Prod.ext
        · exact h_pair_fst
        · exact h_pair_true
      rw [← h_pair_eq]; exact h_pair_in
    have h_vid_honest : isHonestValidator system vid = true :=
      isHonestValidator_of_mem system vid h_sys_nodup h_vid_pair_in
    obtain ⟨bv, h_bv, h_bv_round⟩ := h_all vid h_vid_honest
    have h_round_lt : round < bv.currentRound := by grind
    have h_prop := proposed_for_lt_currentRound system h_sys_nodup k vid bv h_bv round h_round_lt
    obtain ⟨B, h_op⟩ := (hasProposedFor_iff_mem _ vid round).mp h_prop
    rw [h_pr_def]
    apply List.mem_filterMap.mpr
    refine ⟨ValidatorOperation.block_propose vid B round, h_op, ?_⟩
    simp +decide
  show proposers_raw.eraseDups.length ≥ 2 * system.f + 1
  have h_fin_subset : honest_vids.toFinset ⊆ proposers_raw.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact h_subset x hx
  have h_card_le : honest_vids.toFinset.card ≤ proposers_raw.toFinset.card :=
    Finset.card_le_card h_fin_subset
  have h_hv_card : honest_vids.toFinset.card = honest_vids.length :=
    List.toFinset_card_of_nodup h_hv_nodup
  have h_eraseDups_ge_toFinset : ∀ (l : List ValidatorId),
      l.eraseDups.length ≥ l.toFinset.card := by
    intro l
    induction' l using List.reverseRecOn with l a ih
    · rfl
    · simp +decide [ List.eraseDups_append ]
      by_cases h : a ∈ l.toFinset <;> simp_all +decide [ List.removeAll ]
      exact Nat.lt_succ_of_le ‹_›
  have h_pr_ge : proposers_raw.eraseDups.length ≥ proposers_raw.toFinset.card :=
    h_eraseDups_ge_toFinset proposers_raw
  omega

/- T4 (paper §5): post-GST round-termination. For every round and
every honest validator, there is a step at which vid has accepted
≥ 2f+1 distinct authors' round-`round` blocks. Uses the
accept-before-advance gate: at vid's first advance from `round`
to `round+1`, accept is disabled, so vid has accepted every
round-≤-`round` block in the pool (`accepted_at_advance`); the
`allProposedFor` gate ensures all `system.validators.length` ≥ 2f+1
registered validators proposed for `round`, giving that many
distinct-author round-`round` blocks (via `proposeOp_in_pool`). -/
lemma round_termination_aux
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (time : TimeMap) (h_time : time.WellFormed)
    (h_fair : SchedulerFairness system time)
    (hHonest : HonestBFTBound system)
    (h_sys_nodup : ValidatorsNodup system) :
    RoundTermination system (belugaTrace system) := by
  intro round vid h_honest
  unfold HonestBFTBound at hHonest
  obtain ⟨k₀, hk₀_gst⟩ := h_time.2 system.GST
  obtain ⟨bv₀, h_bv₀⟩ := honest_validator_persistent_trace system vid h_honest 0
  have h_bv₀_round : bv₀.currentRound = 0 :=
    getValidator_init_round_zero system vid bv₀ h_bv₀
  obtain ⟨k_target, _, _, h_target_all⟩ :=
    all_honest_eventually_at_round system time h_time h_fair vid h_honest k₀ hk₀_gst (round + 1)
  obtain ⟨bv_target, h_bv_target, h_bv_target_round⟩ := h_target_all vid h_honest
  obtain ⟨k_pre, _, hk_pre_le_t, bv_pre, h_bv_pre, h_bv_pre_round⟩ :=
    round_intermediate_value system vid 0 k_target round
      (Nat.zero_le _) bv₀ bv_target h_bv₀ h_bv_target
      (by rw [h_bv₀_round]; exact Nat.zero_le _)
      (le_trans (Nat.le_succ _) h_bv_target_round)
  obtain ⟨k_a, bv_a, bv_a', _, _, h_a, h_a', h_a_eq, h_a'_eq⟩ :=
    find_advance_step system vid round hk_pre_le_t bv_pre bv_target h_bv_pre h_bv_target
      h_bv_pre_round h_bv_target_round
  refine ⟨k_a, ?_⟩
  have h_nodup_a := belugaTrace_validators_nodup system h_sys_nodup k_a
  have h_advance' : bv_a'.currentRound = bv_a.currentRound + 1 := by rw [h_a_eq, h_a'_eq]
  have h_all_propose :=
    step_advance_implies_allProposedFor system _ vid bv_a bv_a' h_nodup_a h_a h_a' h_advance'
  rw [h_a_eq] at h_all_propose
  have h_blockInv := blockInv_trace system hids k_a
  set acceptedAuthors_raw := (opsAt (belugaTrace system) k_a).filterMap (fun op =>
    match op with
    | .block_accept vid' d =>
        if vid' = vid then authorOfDigest (opsAt (belugaTrace system) k_a) round d else none
    | _ => none) with h_aA_def
  have h_subset : ∀ vid_a, (∃ p ∈ system.validators, p.1 = vid_a) →
      vid_a ∈ acceptedAuthors_raw := by
    intro vid_a ⟨p, h_p_mem, h_p_fst⟩
    have h_prop : hasProposedFor (belugaTrace system k_a) vid_a round = true := by
      unfold allProposedFor at h_all_propose
      rw [List.all_eq_true] at h_all_propose
      have h_pp := h_all_propose p h_p_mem
      simp at h_pp
      rw [h_p_fst] at h_pp
      exact h_pp
    obtain ⟨B, hB_mem⟩ := (hasProposedFor_iff_mem _ vid_a round).mp h_prop
    obtain ⟨hB_in, hB_auth, hB_round⟩ :=
      belugaTrace_proposeOp_in_pool system k_a vid_a B round hB_mem
    have h_R : bv_a.currentRound = round := h_a_eq
    have h_B_le : B.r ≤ round := by rw [hB_round]
    have h_acc_B : hasAcceptedDigest (belugaTrace system k_a) vid B.d = true :=
      accepted_at_advance system h_sys_nodup k_a round vid bv_a bv_a' h_a h_a'
        h_R h_a'_eq B hB_in h_B_le
    have h_acc_op :
        ValidatorOperation.block_accept vid B.d ∈ (belugaTrace system k_a).emittedOperations := by
      unfold hasAcceptedDigest at h_acc_B
      rw [List.any_eq_true] at h_acc_B
      obtain ⟨op, hop_mem, hop_match⟩ := h_acc_B
      cases op with
      | block_accept v d =>
        simp at hop_match
        obtain ⟨h_v, h_d⟩ := hop_match
        rw [h_v, h_d] at hop_mem
        exact hop_mem
      | _ => simp at hop_match
    have h_author : authorOfDigest (belugaTrace system k_a).emittedOperations round B.d
        = some vid_a := by
      unfold authorOfDigest
      have h_pred_B : (match (ValidatorOperation.block_propose vid_a B round) with
            | .block_propose _ block r => block.d == B.d && r == round
            | _ => false) = true := by simp +decide
      rcases h_find : (belugaTrace system k_a).emittedOperations.find?
          (fun op => match op with
            | .block_propose _ block r => block.d == B.d && r == round
            | _ => false) with _ | op_found
      · exfalso
        rw [List.find?_eq_none] at h_find
        exact absurd h_pred_B (by have := h_find _ hB_mem; simp_all)
      · cases op_found with
        | block_propose v block r =>
          have h_pred := List.find?_some h_find
          have h_mem_found := List.mem_of_find?_eq_some h_find
          simp at h_pred
          obtain ⟨h_block_d, h_r⟩ := h_pred
          obtain ⟨h_block_in, h_block_auth, h_block_r⟩ :=
            belugaTrace_proposeOp_in_pool system k_a v block r h_mem_found
          have h_v_bound : v < system.n + 1 := by
            rw [← h_block_auth]
            exact h_blockInv.authorBounded block h_block_in
          have h_p_bound : p.1 < system.n + 1 := hids p h_p_mem
          have h_vid_a_bound : vid_a < system.n + 1 := h_p_fst ▸ h_p_bound
          have h_block_d_canon : block.d = digest system block.r block.author :=
            h_blockInv.canonical block h_block_in
          have h_B_d_canon : B.d = digest system B.r B.author :=
            h_blockInv.canonical B hB_in
          have h_digest_eq : digest system block.r block.author = digest system B.r B.author := by
            rw [← h_block_d_canon, ← h_B_d_canon]; exact h_block_d
          have h_block_v_eq : block.author = v := h_block_auth
          have ⟨_, h_v_eq⟩ : block.r = B.r ∧ block.author = B.author := by
            apply digest_injective system block.r B.r block.author B.author
            · rw [h_block_v_eq]; exact h_v_bound
            · rw [hB_auth]; exact h_vid_a_bound
            · exact h_digest_eq
          have h_v_final : v = vid_a := by
            rw [← h_block_v_eq, h_v_eq, hB_auth]
          grind
        | block_accept v d =>
          have h_pred := List.find?_some h_find
          simp at h_pred
        | block_store v B' =>
          have h_pred := List.find?_some h_find
          simp at h_pred
    rw [h_aA_def]
    apply List.mem_filterMap.mpr
    refine ⟨ValidatorOperation.block_accept vid B.d, h_acc_op, ?_⟩
    simp; exact h_author
  show acceptedAuthors_raw.eraseDups.length ≥ 2 * system.f + 1
  set system_vids := system.validators.map Prod.fst with h_sv_def
  have h_sv_subset : ∀ vid_a ∈ system_vids, vid_a ∈ acceptedAuthors_raw := by
    intro vid_a h_vid_a_mem
    rw [h_sv_def, List.mem_map] at h_vid_a_mem
    exact h_subset vid_a h_vid_a_mem
  have h_fin_subset : system_vids.toFinset ⊆ acceptedAuthors_raw.toFinset := by
    intro x hx; rw [List.mem_toFinset] at hx ⊢; exact h_sv_subset x hx
  have h_card_le : system_vids.toFinset.card ≤ acceptedAuthors_raw.toFinset.card :=
    Finset.card_le_card h_fin_subset
  have h_sv_card : system_vids.toFinset.card = system_vids.length :=
    List.toFinset_card_of_nodup h_sys_nodup
  have h_sv_len : system_vids.length ≥ 2 * system.f + 1 := by
    rw [h_sv_def, List.length_map]
    have h_honest_le :
        (system.validators.filter (fun p => p.2 = true)).length ≤ system.validators.length :=
      List.length_filter_le _ _
    omega
  have h_eraseDups_ge_toFinset : ∀ (l : List ValidatorId),
      l.eraseDups.length ≥ l.toFinset.card := by
    intro l
    induction' l using List.reverseRecOn with l a ih
    · rfl
    · simp +decide [ List.eraseDups_append ]
      by_cases h : a ∈ l.toFinset <;> simp_all +decide [ List.removeAll ]
      exact Nat.lt_succ_of_le ‹_›
  have h_aa_ge : acceptedAuthors_raw.eraseDups.length ≥ acceptedAuthors_raw.toFinset.card :=
    h_eraseDups_ge_toFinset acceptedAuthors_raw
  omega



/-! ## The Beluga §5 post-GST liveness invariant

L1, L2, T1, T3, T4 are each "post-GST eventually X" claims about
`belugaTrace`. They share an underlying inductive structure: each
relies on a form of fairness for honest-validator actions
(propose / accept / store / advance) post-GST. Following the
template used by
[`Beluga/AdmissionInvariant.lean`](AdmissionInvariant.lean), we
package the conclusions as a single bundle predicate, prove each
main theorem locally as a one-line projection, and defer the
inductive proof of the bundle (which threads a compound trace
carrier through the four `tryActFor` branches) to a single
load-bearing theorem.

T2 (Causal availability) is **not** in the bundle — it follows
directly from `causally_closed_trace` proved in
[`Protocol.lean`](Protocol.lean) (the `BlockInv` → `AcceptInv` →
`CausallyClosed` chain). No fairness is needed for it. -/

/-- **Post-GST liveness bundle.**

Bundles the conclusions of paper §5's L1, L2, T1, T3, T4 — every
theorem whose proof requires fairness of honest validator actions
post-GST. Each field is one main-theorem conclusion verbatim:

| field | corresponds to |
|---|---|
| `honest_round_sync` | L1 |
| `honest_round_advance` | L2 |
| `block_availability` | T1 |
| `round_progression` | T3 |
| `round_termination` | T4 |
-/
structure BelugaPostGSTLiveness
    (system : BlockSynchroniserSystem) (time : TimeMap) : Prop where
  /-- L1 (paper §5) — post-GST round entry, *weakened from the
  paper's strict same-round form*. **Finding F-1b** in
  `docs/mechanization-findings.md` and the Stage 2 paper
  additions doc explain the deviation:
  - **Paper L1**: "After GST, all honest validators will enter
    the same round within 3Δ."
  - **Our L1**: "After GST, given an honest validator at round
    `r`, all honest validators reach round `≥ r + 1` within 3Δ."

  The strict same-round form requires either (a) atomic
  round-transition in the model, or (b) the gap-1 currentRound
  invariant + a careful argument that the *first* step at which
  all reach `r+1` has gap = 0. Neither is currently in scope; the
  weakened form captures the lockstep-progress intuition the
  paper relies on without claiming gap-0 stably. -/
  honest_round_sync :
    ∀ vid_ref r k₀, isHonestValidator system vid_ref = true →
      time k₀ ≥ system.GST →
      (∃ bv_ref, (belugaTrace system k₀).getValidator vid_ref = some bv_ref ∧
        bv_ref.currentRound = r) →
      ∃ k', k₀ ≤ k' ∧ time k' ≤ time k₀ + 3 * system.Δ ∧
        ∀ vid, isHonestValidator system vid = true →
          ∃ bv, (belugaTrace system k').getValidator vid = some bv ∧
                bv.currentRound ≥ r + 1
  honest_round_advance :
    ∀ vid r k,
      isHonestValidator system vid = true →
      time k ≥ system.GST →
      (∃ bv, (belugaTrace system k).getValidator vid = some bv ∧ bv.currentRound = r) →
      ∃ k' ≥ k, time k' ≤ time k + 3 * system.Δ ∧
        ∃ bv, (belugaTrace system k').getValidator vid = some bv ∧
              bv.currentRound = r + 1
  block_availability  : BlockAvailability  system (belugaTrace system)
  round_progression   : RoundProgression   system (belugaTrace system)
  round_termination   : RoundTermination   system (belugaTrace system)

/-- The Beluga trace satisfies the post-GST liveness bundle.

This is the load-bearing theorem of paper §5. The proof pattern
mirrors `belugaTrace_admissionWellFormed`: a compound trace
invariant carrying enabledness, action-progression, and
round-synchronisation conjuncts, preserved by every `tryActFor`
branch, projected to each conjunct of `BelugaPostGSTLiveness`.

The **L2 conjunct (`honest_round_advance`)** is discharged inline
here: from the lockstep `SchedulerFairness` (which gives `≥ r + 1`
within `3Δ`), `round_intermediate_value` extracts a step at
*exactly* `r + 1`, with `_h_time.1` (monotonicity) transferring
the time bound. This is a genuine derivation, not a stub.

The other four conjuncts (L1 `honest_round_sync`, T1
`block_availability`, T3 `round_progression`, T4
`round_termination`) are stubs queued for delegation. -/
theorem belugaTrace_satisfies_post_gst_liveness
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (_h_sync : PartiallySynchronous system (belugaTrace system) time)
    (h_fair : SchedulerFairness system time)
    (hHonest : HonestBFTBound system)
    (h_sys_nodup : ValidatorsNodup system) :
    BelugaPostGSTLiveness system time := by
  refine
    { honest_round_sync := ?_
      honest_round_advance := ?_
      block_availability := ?_
      round_progression := ?_
      round_termination := ?_ }
  · -- L1 (honest_round_sync), weakened (F-1b): direct h_fair invocation.
    intro vid_ref r k₀ _hvid_ref htime ⟨bv_ref, hbv_ref, hrnd_ref⟩
    exact h_fair k₀ r htime ⟨vid_ref, bv_ref, _hvid_ref, hbv_ref, hrnd_ref⟩
  · -- L2 (honest_round_advance): h_fair + round_intermediate_value.
    intro vid r k hvid htime ⟨bv, hbv, hrnd⟩
    obtain ⟨k', hk'le, hk'time, hk'all⟩ :=
      h_fair k r htime ⟨vid, bv, hvid, hbv, hrnd⟩
    obtain ⟨bv', hbv', hbv'rnd⟩ := hk'all vid hvid
    have hle_r : bv.currentRound ≤ r + 1 := by rw [hrnd]; exact Nat.le_succ r
    obtain ⟨kc, hkc_lo, hkc_hi, bvc, hbvc, hrnd_eq⟩ :=
      round_intermediate_value system vid k k' (r + 1) hk'le bv bv' hbv hbv'
        hle_r hbv'rnd
    have htime_kc : time kc ≤ time k + 3 * system.Δ :=
      le_trans (h_time.1 kc k' hkc_hi) hk'time
    exact ⟨kc, hkc_lo, htime_kc, bvc, hbvc, hrnd_eq⟩
  · -- T1: store-before-advance gate at vid's first post-acceptance advance step.
    intro k vid d h_honest h_acc
    obtain ⟨k_post, hk_post_le, hk_post_gst⟩ : ∃ k', k ≤ k' ∧ time k' ≥ system.GST := by
      obtain ⟨k', hk'⟩ := h_time.2 system.GST
      exact ⟨max k k', le_max_left _ _, le_trans hk' (h_time.1 _ _ (le_max_right _ _))⟩
    obtain ⟨bv_post, h_bv_post⟩ :=
      honest_validator_persistent_trace system vid h_honest k_post
    set r := bv_post.currentRound with hr_def
    obtain ⟨k_target, hk_target_le, _, h_target_all⟩ :=
      h_fair k_post r hk_post_gst ⟨vid, bv_post, h_honest, h_bv_post, hr_def.symm⟩
    obtain ⟨bv_target, h_bv_target, hbv_target_rnd⟩ := h_target_all vid h_honest
    obtain ⟨k_a, bv_a, bv_a', hk_a_le, hk_a_lt, h_a, h_a', h_a_eq, h_a'_eq⟩ :=
      find_advance_step system vid r hk_target_le bv_post bv_target h_bv_post h_bv_target
        hr_def.symm hbv_target_rnd
    have h_nodup_a := belugaTrace_validators_nodup system h_sys_nodup k_a
    have h_advance : bv_a'.currentRound = bv_a.currentRound + 1 := by rw [h_a_eq, h_a'_eq]
    have h_stored_gate :=
      step_advance_implies_stored system (belugaTrace system k_a) vid bv_a bv_a'
        h_nodup_a h_a (by show (belugaTrace system (k_a + 1)).getValidator vid = some bv_a'
                          exact h_a') h_advance
    have h_acc_at_a : HasAccepted (belugaTrace system k_a) vid d := by
      have h_le : k ≤ k_a := le_trans hk_post_le hk_a_le
      have h_mono : ∀ op ∈ (belugaTrace system k).emittedOperations,
          op ∈ (belugaTrace system k_a).emittedOperations := by
        clear * - h_le
        induction h_le with
        | refl => intro _ h; exact h
        | step _ ih => intro op hop; exact step_emittedOperations_monotone system _ op (ih op hop)
      exact h_mono _ h_acc
    have h_acc_bool : hasAcceptedDigest (belugaTrace system k_a) vid d = true := by
      unfold hasAcceptedDigest
      rw [List.any_eq_true]
      exact ⟨_, h_acc_at_a, by simp +decide⟩
    have h_ai := acceptInv_trace system vid hids k_a
    obtain ⟨B, hB_mem, hB_d⟩ := h_ai.acceptedBlockExists d h_acc_at_a
    have h_acc_B : hasAcceptedDigest (belugaTrace system k_a) vid B.d = true := by
      rw [hB_d]; exact h_acc_bool
    have h_sto_B : hasStoredDigest (belugaTrace system k_a) vid B.d = true :=
      h_stored_gate B hB_mem h_acc_B
    unfold hasStoredDigest at h_sto_B
    rw [List.any_eq_true] at h_sto_B
    obtain ⟨op, hop_mem, hop_match⟩ := h_sto_B
    refine ⟨k_a, le_trans hk_post_le hk_a_le, ?_⟩
    cases op with
    | block_store v B' =>
      simp at hop_match
      obtain ⟨h_v, h_d⟩ := hop_match
      refine ⟨B', ?_, ?_⟩
      · show ValidatorOperation.block_store vid B' ∈ (belugaTrace system k_a).emittedOperations
        rw [h_v] at hop_mem; exact hop_mem
      · rw [h_d]; exact hB_d
    | _ => simp at hop_match
  · exact round_progression_aux system time h_time h_fair hHonest h_sys_nodup
  · exact round_termination_aux system hids time h_time h_fair hHonest h_sys_nodup

/-! ## Lemmas 1, 2 and Theorems 1–4 (local derivations from the bundle)

L1, L2, T1, T3, T4 are one-line projections of the bundle. T2
derives directly from the trace-invariant `causally_closed_trace`
in `Protocol.lean` and does not require fairness. -/

/-- **Lemma 1 (paper §5)** — *weakened from the strict same-round
form*. After GST, given an honest validator at round `r`, all
honest validators reach round `≥ r + 1` within `3Δ`.

The paper's original L1 statement is "After GST, all honest
validators will enter the same round within 3Δ" — our weakened
version replaces "the same round" with "at least round r + 1",
because the strict same-round form requires either atomic
round transitions in the trace model or a gap-1 currentRound
invariant we don't currently have. See finding **F-1b** in
`docs/mechanization-findings.md` and the Stage 2 paper-additions
doc for the full discussion. -/
theorem lemma1_honest_round_entry
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (h_fair : SchedulerFairness system time)
    (hHonest : HonestBFTBound system)
    (h_sys_nodup : ValidatorsNodup system) :
    ∀ vid_ref r k₀, isHonestValidator system vid_ref = true →
      time k₀ ≥ system.GST →
      (∃ bv_ref, (belugaTrace system k₀).getValidator vid_ref = some bv_ref ∧
        bv_ref.currentRound = r) →
      ∃ k', k₀ ≤ k' ∧ time k' ≤ time k₀ + 3 * system.Δ ∧
        ∀ vid, isHonestValidator system vid = true →
          ∃ bv, (belugaTrace system k').getValidator vid = some bv ∧
                bv.currentRound ≥ r + 1 :=
  (belugaTrace_satisfies_post_gst_liveness system hids time h_time h_sync h_fair hHonest h_sys_nodup).honest_round_sync

/-- **Lemma 2 (paper §5).** After GST, an honest validator at round
`r` enters round `r + 1` within `3Δ`. -/
theorem lemma2_round_latency
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (h_fair : SchedulerFairness system time)
    (hHonest : HonestBFTBound system)
    (h_sys_nodup : ValidatorsNodup system) :
    ∀ vid r k,
      isHonestValidator system vid = true →
      time k ≥ system.GST →
      (∃ bv, (belugaTrace system k).getValidator vid = some bv ∧ bv.currentRound = r) →
      ∃ k' ≥ k, time k' ≤ time k + 3 * system.Δ ∧
        ∃ bv, (belugaTrace system k').getValidator vid = some bv ∧
              bv.currentRound = r + 1 :=
  (belugaTrace_satisfies_post_gst_liveness system hids time h_time h_sync h_fair hHonest h_sys_nodup).honest_round_advance

/-- **Theorem 1 (paper §5).** Beluga satisfies Block availability. -/
theorem theorem1_block_availability
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (h_fair : SchedulerFairness system time)
    (hHonest : HonestBFTBound system)
    (h_sys_nodup : ValidatorsNodup system) :
    BlockAvailability system (belugaTrace system) :=
  (belugaTrace_satisfies_post_gst_liveness system hids time h_time h_sync h_fair hHonest h_sys_nodup).block_availability

/-- **Theorem 2 (paper §5).** Beluga satisfies Causal availability.

Direct from `causallyClosed_trace` in `Protocol.lean`: at every
state in the trace, accepted digests have all their causal-ancestor
digests already accepted. So the `Eventually` quantifier in
`CausalAvailability` is satisfied at the current step (`k' = k`).
No fairness needed; only the standard `ValidIds` BFT side condition
(finding F-8(b)) for the underlying digest-injectivity step. -/
theorem theorem2_causal_availability
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (_time : TimeMap)
    (_h_time : _time.WellFormed)
    (_h_sync : PartiallySynchronous system (belugaTrace system) _time)
    (_h_fair : SchedulerFairness system _time) :
    CausalAvailability system (belugaTrace system) := by
  intro k vid d B _h_honest h_acc h_get B' h_reach
  refine ⟨k, le_refl k, ?_⟩
  have h_B_d : B.d = d := by
    unfold getBlockByDigest at h_get
    have := List.find?_some h_get
    simpa using this
  have hcc := causallyClosed_trace system vid hids k
  rw [← h_B_d] at h_acc
  exact hcc B h_acc B' h_reach

/-- **Theorem 3 (paper §5).** Beluga satisfies Round-Progression. -/
theorem theorem3_round_progression
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (h_fair : SchedulerFairness system time)
    (hHonest : HonestBFTBound system)
    (h_sys_nodup : ValidatorsNodup system) :
    RoundProgression system (belugaTrace system) :=
  (belugaTrace_satisfies_post_gst_liveness system hids time h_time h_sync h_fair hHonest h_sys_nodup).round_progression

/-- **Theorem 4 (paper §5).** Beluga satisfies Round-Termination. -/
theorem theorem4_round_termination
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (h_fair : SchedulerFairness system time)
    (hHonest : HonestBFTBound system)
    (h_sys_nodup : ValidatorsNodup system) :
    RoundTermination system (belugaTrace system) :=
  (belugaTrace_satisfies_post_gst_liveness system hids time h_time h_sync h_fair hHonest h_sys_nodup).round_termination

/-- **Beluga is a block synchronizer (corollary of Theorems 1–4).**

The headline statement of paper §5: Beluga's induced trace satisfies
all four properties of Definition 1, under the timing model and
scheduler-fairness assumption. -/
theorem belugaTrace_isBlockSynchronizer
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (h_fair : SchedulerFairness system time)
    (hHonest : HonestBFTBound system)
    (h_sys_nodup : ValidatorsNodup system) :
    BlockSynchronizer system (belugaTrace system) :=
  ⟨theorem3_round_progression system hids time h_time h_sync h_fair hHonest h_sys_nodup,
   theorem4_round_termination system hids time h_time h_sync h_fair hHonest h_sys_nodup,
   theorem1_block_availability system hids time h_time h_sync h_fair hHonest h_sys_nodup,
   theorem2_causal_availability system hids time h_time h_sync h_fair⟩

end Theorems
end Beluga
end BlockSynchroniser
