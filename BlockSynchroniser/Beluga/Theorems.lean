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

/-! ### Scheduler fairness (paper Assumption 2, made explicit)

The paper's prose proofs of L1, L2, and T1–T4 silently assume that
honest validators *act promptly*: whenever the protocol of §4 enables
a local action (propose/accept/store/advance), an honest validator
performs it within `Δ`. Without this, the paper's `3Δ`-bounded round
synchronisation (and any "eventually" claim downstream) does not
hold — see `docs/paper-feedback-l1-l2-fairness.md` for a paper-level
counterexample.

We surface the assumption at *round granularity* (which is what our
trace model exposes): post-GST, when some honest validator reaches
round `r`, every honest validator reaches round `r` within `3Δ`. This
is the round-level shadow of the per-action assumption.

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
              bv.currentRound ≥ r

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

Proof: structural case analysis on `tryActFor`'s four branches. Aristotle r3a
discharged this with a `grind` chain that times out in our build context;
queued as round 3a-followup.
-/
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

Proof body times out under our build context (Aristotle r3a's structural
chain through doAccept/doStore/doAdvance/doPropose hits a heartbeat
limit on `isDefEq` we can't easily push past). Queued as round 3a-followup.
-/
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
  honest_round_sync :
    ∀ vid₁ vid₂,
      isHonestValidator system vid₁ = true →
      isHonestValidator system vid₂ = true →
      ∀ k, time k ≥ system.GST + 3 * system.Δ →
        match (belugaTrace system k).getValidator vid₁,
              (belugaTrace system k).getValidator vid₂ with
        | some bv₁, some bv₂ => bv₁.currentRound = bv₂.currentRound
        | _, _ => False
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
mirrors `belugaTrace_admissionWellFormed`: a private compound trace
invariant carrying enabledness, action-progression, and
round-synchronisation conjuncts, preserved by every `tryActFor`
branch, projected to each conjunct of `BelugaPostGSTLiveness`.

Currently a stub — the inductive proof is queued for delegation. -/
theorem belugaTrace_satisfies_post_gst_liveness
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (_h_time : time.WellFormed)
    (_h_sync : PartiallySynchronous system (belugaTrace system) time)
    (_h_fair : SchedulerFairness system time) :
    BelugaPostGSTLiveness system time := by
  sorry

/-! ## Lemmas 1, 2 and Theorems 1–4 (local derivations from the bundle)

L1, L2, T1, T3, T4 are one-line projections of the bundle. T2
derives directly from the trace-invariant `causally_closed_trace`
in `Protocol.lean` and does not require fairness. -/

/-- **Lemma 1 (paper §5).** After GST, all honest validators enter
the same round within `3Δ`. -/
theorem lemma1_honest_round_entry
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (h_fair : SchedulerFairness system time) :
    ∀ vid₁ vid₂,
      isHonestValidator system vid₁ = true →
      isHonestValidator system vid₂ = true →
      ∀ k, time k ≥ system.GST + 3 * system.Δ →
        match (belugaTrace system k).getValidator vid₁,
              (belugaTrace system k).getValidator vid₂ with
        | some bv₁, some bv₂ => bv₁.currentRound = bv₂.currentRound
        | _, _ => False :=
  (belugaTrace_satisfies_post_gst_liveness system time h_time h_sync h_fair).honest_round_sync

/-- **Lemma 2 (paper §5).** After GST, an honest validator at round
`r` enters round `r + 1` within `3Δ`. -/
theorem lemma2_round_latency
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (h_fair : SchedulerFairness system time) :
    ∀ vid r k,
      isHonestValidator system vid = true →
      time k ≥ system.GST →
      (∃ bv, (belugaTrace system k).getValidator vid = some bv ∧ bv.currentRound = r) →
      ∃ k' ≥ k, time k' ≤ time k + 3 * system.Δ ∧
        ∃ bv, (belugaTrace system k').getValidator vid = some bv ∧
              bv.currentRound = r + 1 :=
  (belugaTrace_satisfies_post_gst_liveness system time h_time h_sync h_fair).honest_round_advance

/-- **Theorem 1 (paper §5).** Beluga satisfies Block availability. -/
theorem theorem1_block_availability
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (h_fair : SchedulerFairness system time) :
    BlockAvailability system (belugaTrace system) :=
  (belugaTrace_satisfies_post_gst_liveness system time h_time h_sync h_fair).block_availability

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
  -- Eventually trace k P := ∃ k' ≥ k, P k' (trace k'). Take k' = k.
  refine ⟨k, le_refl k, ?_⟩
  -- `getBlockByDigest = some B` means B has digest d.
  have h_B_d : B.d = d := by
    unfold getBlockByDigest at h_get
    have := List.find?_some h_get
    simpa using this
  -- Apply causal closure: accepted digest d = B.d implies ancestors accepted.
  have hcc := causallyClosed_trace system vid hids k
  rw [← h_B_d] at h_acc
  exact hcc B h_acc B' h_reach

/-- **Theorem 3 (paper §5).** Beluga satisfies Round-Progression. -/
theorem theorem3_round_progression
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (h_fair : SchedulerFairness system time) :
    RoundProgression system (belugaTrace system) :=
  (belugaTrace_satisfies_post_gst_liveness system time h_time h_sync h_fair).round_progression

/-- **Theorem 4 (paper §5).** Beluga satisfies Round-Termination. -/
theorem theorem4_round_termination
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (h_time : time.WellFormed)
    (h_sync : PartiallySynchronous system (belugaTrace system) time)
    (h_fair : SchedulerFairness system time) :
    RoundTermination system (belugaTrace system) :=
  (belugaTrace_satisfies_post_gst_liveness system time h_time h_sync h_fair).round_termination

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
    (h_fair : SchedulerFairness system time) :
    BlockSynchronizer system (belugaTrace system) :=
  ⟨theorem3_round_progression system time h_time h_sync h_fair,
   theorem4_round_termination system time h_time h_sync h_fair,
   theorem1_block_availability system time h_time h_sync h_fair,
   theorem2_causal_availability system hids time h_time h_sync h_fair⟩

end Theorems
end Beluga
end BlockSynchroniser
