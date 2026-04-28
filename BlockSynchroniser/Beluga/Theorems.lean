/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Beluga's main theorems (paper §5).

This file is the paper-facing layer. It packages the paper's
partial-synchrony assumptions (Sections 2, 4.2, 4.3) into the
`BelugaWithPullFairness` bundle and proves, against the network-aware
trace `networkTraceWithPull`, the §5 lemmas

* L1 — round entry within `4Δ` (`lemma1_honest_round_entry`)

and the §5 theorems

* T1 — Block Availability (`network_theorem1_block_availability_withPull`)
* T2 — Causal Availability (`network_theorem2_causal_availability_withPull`)
* T3 — Round Progression  (`network_theorem3_round_progression_withPull`)
* T4 — Round Termination  (`network_theorem4_round_termination_proved`)

The §5 headline `beluga_isBlockSynchronizer` consumes the bundle once
and concludes that Beluga's network-aware trace satisfies all four
block-synchronizer properties — fully derived from the paper-stated
liveness primitives, with no `Eventual*` axioms.

The relational synchronous-style invariants of Beluga's executable
`step` function (round monotonicity, advance inversion, etc.) are
also collected here as supporting infrastructure inside the
`Theorems` namespace.
-/
import Mathlib.Tactic
import BlockSynchroniser.System
import BlockSynchroniser.Properties
import BlockSynchroniser.Timing
import BlockSynchroniser.Beluga.Protocol
import BlockSynchroniser.Beluga.AdmissionInvariant
import BlockSynchroniser.Beluga.Network

namespace BlockSynchroniser
namespace Beluga

namespace Network

/-! ## §5 paper-liveness bundle -/

/-- **`BelugaPartialSynchrony`** packages the paper's §2 + §4.2 +
§4.3 post-GST liveness assumptions in event-triggered form. The
round-advance liveness (`catchUpLiveness`, paper §4.2 rules
(i)/(iii)): a validator catches up to a leader's round within `4Δ`,
but no claim is made when no leader is ahead — consistent with
§4.2 rule-(ii)'s timeout `T_rd = 5Δ` upper-bounding time-in-round
in the absence of a quorum or leader trigger.

| Field                | Paper reference                                    |
|----------------------|----------------------------------------------------|
| `timeMonotone`       | global clock monotonicity                          |
| `timeUnbounded`      | the trace makes wall-clock progress                |
| `networkDelivery`    | §2 — `Δ`-delivery                                  |
| `boundedRoundSpread` | §4.2 — protocol synchronization (gap ≤ 1)          |
| `acceptScheduling`   | §4.2 — accept-action liveness                      |
| `inPoolDelivery`     | §4.3 — universal in-pool delivery (push ∪ pull)    |
| `catchUpLiveness`    | §4.2 rules (i)/(iii) — catch-up to leader in `4Δ`  |

Paper §5 Lemma 1 (`lemma1_honest_round_entry`) is proved against
this bundle alone.
-/
structure BelugaPartialSynchrony
    (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop where
  /-- The wall clock advances monotonically along the trace. -/
  timeMonotone       : ∀ i j, i ≤ j → time i ≤ time j
  /-- The wall clock is unbounded: the trace eventually passes any time. -/
  timeUnbounded      : ∀ T, ∃ k, time k ≥ T
  /-- Paper §2: post-GST, every push message between honest validators
  is delivered within `Δ`. -/
  networkDelivery    : NetworkDeliveryWithPull system time
  /-- Paper §4.2 protocol-synchronization: post-GST, the rounds of any
  two honest validators differ by at most one. -/
  boundedRoundSpread : BoundedRoundSpread_networkTraceWithPull system time
  /-- Paper §4.2: post-GST, an honest validator with an acceptable
  in-pool block accepts it within `Δ`. -/
  acceptScheduling   : AcceptScheduling system time
  /-- Paper §4.3: post-GST, every block in the global pool is
  eventually known to every honest validator (via push for honest
  authors, or via the pull mechanism otherwise). -/
  inPoolDelivery     : NetworkInPoolDeliveryWithPull system time
  /-- Paper §4.2 rules (i)/(iii) (event-triggered): post-GST, an
  honest validator at a strictly lower round than some honest leader
  catches up to the leader's round within `4Δ`. -/
  catchUpLiveness    : CatchUpLiveness system time

/-- **`BelugaWithPullFairness`** extends `BelugaPartialSynchrony`
with the paper §4.2 rule-(ii) per-round timeout `T_rd = 5Δ`:
post-GST, every honest validator advances rounds within `5Δ`,
unconditionally (whether or not a quorum or leader sighting fires
first). Consumed by the §5 theorems T1–T4 to drive unbounded round
progression. -/
structure BelugaWithPullFairness
    (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop
    extends BelugaPartialSynchrony system time where
  /-- Paper §4.2 rule (ii): the per-round timeout `T_rd = 5Δ` —
  post-GST, every honest validator advances rounds within `5Δ`. -/
  timeoutAdvance     : TimeoutAdvanceWithPull system time

end Network

namespace Theorems

open Properties Network

/-! ## Supporting infrastructure for `belugaTrace`

Each theorem says "the trace induced by Beluga's executable protocol
satisfies Definition 1.X". The statements are stated against the
*relational* `HonestStep` semantics — `belugaTrace` (the executable
schedule) is one specific witness, but the theorems generalize to any
trace whose every step satisfies `HonestStep`. -/

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

Proof: structural case analysis on `tryActFor`'s four branches.
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

Proof: structural case analysis on `tryActFor`'s four branches via the
per-action helpers `doAccept_round`, `doStore_round`, `doAdvance_round`,
`doPropose_getValidator`.
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


/-! ## Liveness-support helper lemmas

These lemmas establish structural properties of the trace that are
needed by the post-GST liveness bundle proof — in particular the
*intermediate-value theorem* for rounds (`round_intermediate_value`),
which underpins the L2 derivation from the lockstep `SchedulerFairness`.

-/

/-
The `step` function increases any validator's `currentRound` by at most 1.
-/
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
lemma honest_validator_persistent_trace (system : BlockSynchroniserSystem)
    (vid : ValidatorId) (hvid : isHonestValidator system vid = true) (k : Nat) :
    ∃ bv, (belugaTrace system k).getValidator vid = some bv := by
  exact Nat.recOn k ( getValidator_init_some system vid hvid ) fun n ihn => getValidator_persistent _ _ _ ihn

/-
Round monotonicity across arbitrary trace steps:
if `k₁ ≤ k₂` and `vid` is present at both steps, its round does not decrease.
-/
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
same-round form to the lockstep-progress form, since the protocol's
advance rule allows transient states where two honest validators
differ by one round. -/

/-! ### Side conditions threaded through the bundle

Two paper-§2 side conditions surface in nearly every theorem in
this file. Naming them lets the public signatures stay readable
and centralizes their justification. -/

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
end Theorems

namespace Network

/-! ## §5 Lemma 1 — round entry within `4Δ`

Paper §5 Lemma 1: *"After GST, if round `r` is the highest round
that honest validators are in at some time `t`, then all honest
validators will enter round `r` by `t + 4Δ`."*

The proof consumes only `BelugaPartialSynchrony` — the
paper-faithful weaker bundle whose advancement primitive
(`catchUpLiveness`) is event-triggered, matching the §4.2 rules
(i)/(iii). It does *not* consume the over-strong
`actionScheduling` ("rounds advance within `Δ` unconditionally"),
which would conflict with §4.2 rule-(ii)'s timeout `T_rd = 5Δ`.

**Proof structure:**
1. By `boundedRoundSpread`, every honest validator is at round
   `r` or `r-1` at step `k₀`.
2. For each honest validator at round `< r`, apply `catchUpLiveness`
   with `vid_lead = vid_ref` (the witness at round `r`): get a
   per-validator step within `4Δ` at which the validator has
   reached round `≥ r`.
3. For each honest validator at round `≥ r`, no catch-up is
   needed; round monotonicity preserves the bound.
4. Iterate over `system.validators`, taking the max of per-validator
   steps. The max's wall-clock time is ≤ `time k₀ + 4Δ`
   (each component is ≤ that bound, and `time(max k₁ k₂)` equals
   `time k₁` or `time k₂`).
5. Round monotonicity extends each per-validator catch-up to the
   common max step. -/

/-- Forward: `(vid, true) ∈ system.validators → isHonestValidator system vid = true`.
Local copy for use ahead of `network_isHonestValidator_of_mem` (defined later
in this file). -/
private lemma isHonest_of_mem_local
    (system : BlockSynchroniserSystem) (vid : ValidatorId)
    (h_mem : (vid, true) ∈ system.validators) :
    isHonestValidator system vid = true := by
  unfold isHonestValidator BlockSynchroniserSystem.isHonest
  have h_find : system.validators.find? (fun p => p.1 == vid) = some (vid, true) :=
    find?_of_mem_nodup _ vid true h_mem system.validatorsNodup
  have h_pred_eq :
      (fun (x : ValidatorId × Bool) => match x with | (vid_1, _) => decide (vid_1 = vid))
        = (fun p => p.1 == vid) := by
    funext p
    cases p
    show decide _ = (_ == _)
    rfl
  rw [h_pred_eq, h_find]

/-- Converse of `isHonest_of_mem_local`: if
`isHonestValidator system vid = true`, then `(vid, true)` is in
`system.validators`. -/
private lemma mem_validators_of_isHonest
    {system : BlockSynchroniserSystem} {vid : ValidatorId}
    (h : isHonestValidator system vid = true) :
    (vid, true) ∈ system.validators := by
  unfold isHonestValidator BlockSynchroniserSystem.isHonest at h
  match h_some : system.validators.find? (fun p => p.1 = vid) with
  | none => rw [h_some] at h; exact absurd h (by simp)
  | some p =>
    rw [h_some] at h
    have h_p_in := List.mem_of_find?_eq_some h_some
    have h_match := List.find?_some h_some
    have h_p1 : p.1 = vid := by simpa using h_match
    have h_p2 : p.2 = true := h
    have h_p_eq : p = (vid, true) := by
      obtain ⟨a, b⟩ := p
      simp at h_p1 h_p2
      subst h_p1; subst h_p2; rfl
    rw [← h_p_eq]; exact h_p_in

/-- Helper for `lemma1_honest_round_entry`: by induction on a list of
validators, find a single step `k'` post-`k₀` (within `4Δ`) at which
every honest validator in the list is at round `≥ r`. The witness
step is the max of per-validator catch-up steps; round monotonicity
extends each catch-up to the common max. -/
private lemma lemma1_witness_for_validator_list
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h : BelugaPartialSynchrony system time)
    (r : Round) (k₀ : Nat)
    (h_post_gst : time k₀ ≥ system.GST)
    (vid_ref : ValidatorId) (bv_ref : BelugaValidator)
    (h_honest_ref : isHonestValidator system vid_ref = true)
    (h_bv_ref : (networkTraceWithPull system time k₀).base.getValidator vid_ref = some bv_ref)
    (h_round_ref : bv_ref.currentRound = r) :
    ∀ (vs : List (ValidatorId × Bool)),
      (∀ p ∈ vs, p.2 = true → isHonestValidator system p.1 = true) →
      ∃ k', k₀ ≤ k' ∧ time k' ≤ time k₀ + 4 * system.Δ ∧
        ∀ p ∈ vs, p.2 = true →
          ∃ bv, (networkTraceWithPull system time k').base.getValidator p.1 = some bv ∧
                bv.currentRound ≥ r := by
  intro vs
  induction vs with
  | nil =>
    intro _
    refine ⟨k₀, le_refl k₀, ?_, ?_⟩
    · have : 0 ≤ 4 * system.Δ := Nat.zero_le _
      omega
    · intro p h_mem; simp at h_mem
  | cons hd vs_t ih =>
    intro h_premise
    have h_vs_t_premise : ∀ p ∈ vs_t, p.2 = true → isHonestValidator system p.1 = true :=
      fun p h_mem h_b => h_premise p (List.mem_cons_of_mem _ h_mem) h_b
    obtain ⟨k_t, hk_t_lo, hk_t_hi, h_vs_t_step⟩ := ih h_vs_t_premise
    by_cases h_hd_b : hd.2 = true
    · -- hd is honest
      have h_hd_honest : isHonestValidator system hd.1 = true :=
        h_premise hd List.mem_cons_self h_hd_b
      obtain ⟨bv_hd, h_bv_hd⟩ := network_honest_validator_persistent_traceWithPull
        system time hd.1 h_hd_honest k₀
      by_cases h_hd_round : bv_hd.currentRound ≥ r
      · -- hd already at round ≥ r at k₀; reuse k_t
        refine ⟨k_t, hk_t_lo, hk_t_hi, ?_⟩
        intro p h_mem h_p_b
        rw [List.mem_cons] at h_mem
        rcases h_mem with h_eq | h_in_t
        · -- p = hd; transport via h_eq
          obtain ⟨bv_hd_t, h_bv_hd_t⟩ := network_honest_validator_persistent_traceWithPull
            system time hd.1 h_hd_honest k_t
          refine ⟨bv_hd_t, ?_, ?_⟩
          · rw [h_eq]; exact h_bv_hd_t
          · have h_mono := network_round_monotone_traceWithPull system time hd.1
              k₀ bv_hd h_bv_hd k_t hk_t_lo bv_hd_t h_bv_hd_t
            exact le_trans h_hd_round h_mono
        · exact h_vs_t_step p h_in_t h_p_b
      · -- hd at round < r; apply catchUpLiveness with leader = vid_ref
        push_neg at h_hd_round
        have h_lt : bv_hd.currentRound < bv_ref.currentRound := by
          rw [h_round_ref]; exact h_hd_round
        obtain ⟨k_hd, bv_hd', hk_hd_lo, hk_hd_hi, h_bv_hd', h_round_hd'⟩ :=
          h.catchUpLiveness k₀ hd.1 bv_hd vid_ref bv_ref h_hd_honest h_honest_ref
            h_post_gst h_bv_hd h_bv_ref h_lt
        refine ⟨max k_hd k_t, le_trans hk_hd_lo (le_max_left k_hd k_t), ?_, ?_⟩
        · -- time bound: max k_hd k_t = k_hd or k_t; either has time ≤ time k₀ + 4Δ
          by_cases h_le : k_hd ≤ k_t
          · rw [max_eq_right h_le]; exact hk_t_hi
          · push_neg at h_le
            rw [max_eq_left (Nat.le_of_lt h_le)]; exact hk_hd_hi
        · intro p h_mem h_p_b
          rw [List.mem_cons] at h_mem
          rcases h_mem with h_eq | h_in_t
          · -- p = hd; transport via h_eq
            obtain ⟨bv_hd_final, h_bv_hd_final⟩ := network_honest_validator_persistent_traceWithPull
              system time hd.1 h_hd_honest (max k_hd k_t)
            refine ⟨bv_hd_final, ?_, ?_⟩
            · rw [h_eq]; exact h_bv_hd_final
            · -- bv_hd_final.currentRound ≥ bv_hd'.currentRound ≥ bv_ref.currentRound = r
              have h_mono := network_round_monotone_traceWithPull system time hd.1
                k_hd bv_hd' h_bv_hd' (max k_hd k_t) (le_max_left _ _) bv_hd_final h_bv_hd_final
              have h_step : r ≤ bv_hd'.currentRound := by
                rw [← h_round_ref]; exact h_round_hd'
              exact le_trans h_step h_mono
          · obtain ⟨bv_old, h_bv_old, h_round_old⟩ := h_vs_t_step p h_in_t h_p_b
            obtain ⟨bv_final, h_bv_final⟩ := network_honest_validator_persistent_traceWithPull
              system time p.1 (h_vs_t_premise p h_in_t h_p_b) (max k_hd k_t)
            refine ⟨bv_final, h_bv_final, ?_⟩
            have h_mono := network_round_monotone_traceWithPull system time p.1
              k_t bv_old h_bv_old (max k_hd k_t) (le_max_right _ _) bv_final h_bv_final
            exact le_trans h_round_old h_mono
    · -- hd is byzantine; the cons-case for hd is vacuous (its bool ≠ true)
      refine ⟨k_t, hk_t_lo, hk_t_hi, ?_⟩
      intro p h_mem h_p_b
      rw [List.mem_cons] at h_mem
      rcases h_mem with h_eq | h_in_t
      · rw [h_eq] at h_p_b; exact absurd h_p_b h_hd_b
      · exact h_vs_t_step p h_in_t h_p_b

/-- **Lemma 1 (paper §5).** If `r` is the highest round any honest
validator is in at step `k₀` post-GST, then within `4Δ` every honest
validator is at round `≥ r`. Consumes only `BelugaPartialSynchrony`. -/
theorem lemma1_honest_round_entry
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h : BelugaPartialSynchrony system time) :
    ∀ (r : Round) (k₀ : Nat),
      time k₀ ≥ system.GST →
      (∃ vid_ref bv_ref,
        isHonestValidator system vid_ref = true ∧
        (networkTraceWithPull system time k₀).base.getValidator vid_ref = some bv_ref ∧
        bv_ref.currentRound = r) →
      ∃ k', k₀ ≤ k' ∧ time k' ≤ time k₀ + 4 * system.Δ ∧
        ∀ vid, isHonestValidator system vid = true →
          ∃ bv, (networkTraceWithPull system time k').base.getValidator vid = some bv ∧
                bv.currentRound ≥ r := by
  intro r k₀ h_post_gst ⟨vid_ref, bv_ref, h_honest_ref, h_bv_ref, h_round_ref⟩
  -- Premise for the helper: every honest pair in system.validators has the corresponding isHonestValidator.
  have h_premise : ∀ p ∈ system.validators, p.2 = true → isHonestValidator system p.1 = true := by
    intro p h_mem h_b
    have h_pair_mem : (p.1, true) ∈ system.validators := by
      have h_p_eq : p = (p.1, true) := by
        obtain ⟨a, b⟩ := p; simp at h_b ⊢; exact h_b
      rw [← h_p_eq]; exact h_mem
    exact isHonest_of_mem_local system p.1 h_pair_mem
  obtain ⟨k', hk'_lo, hk'_hi, h_step⟩ :=
    lemma1_witness_for_validator_list h r k₀ h_post_gst vid_ref bv_ref
      h_honest_ref h_bv_ref h_round_ref system.validators h_premise
  refine ⟨k', hk'_lo, hk'_hi, ?_⟩
  intro vid h_vid_honest
  exact h_step (vid, true) (mem_validators_of_isHonest h_vid_honest) rfl

/-! ## §5 eventual-acceptance predicates

`EventualCausalAcceptance` and `EventualRoundAcceptance` are the two
paper-implicit liveness conjuncts in §5's T2 and T4 proofs. They are
defined here on a generic `Trace BelugaState` so the with-pull track
below can prove them as theorems (rather than take them as axioms). -/

/-- For any honest validator that has accepted some digest `d`
corresponding to a block `B`, every causal ancestor `B'` of `B` is
eventually accepted by `vid`. -/
def EventualCausalAcceptance (system : BlockSynchroniserSystem)
    (trace : Trace BelugaState) : Prop :=
  ∀ k vid d B, isHonestValidator system vid = true →
    HasAccepted (trace k) vid d →
    getBlockByDigest (trace k) d = some B →
    ∀ B', Reaches (trace k) B B' →
      ∃ k', k ≤ k' ∧ HasAccepted (trace k') vid B'.d

/-- Every honest validator eventually accepts `2f + 1` distinct
authors' round-`r` blocks. -/
def EventualRoundAcceptance (system : BlockSynchroniserSystem)
    (trace : Trace BelugaState) : Prop :=
  ∀ round vid, isHonestValidator system vid →
    ∃ k,
      let ops := opsAt trace k
      let acceptedAuthors : List ValidatorId :=
        ops.filterMap (fun op =>
          match op with
          | .block_accept vid' d =>
            if vid' = vid then authorOfDigest ops round d else none
          | _ => none)
        |>.eraseDups
      acceptedAuthors.length ≥ 2 * system.f + 1

/-! ## `EventualRoundAcceptance` as a derived theorem -/

/-- The pull-mechanism analog of `networkBelugaTrace`. -/
def networkBelugaTraceWithPull (system : BlockSynchroniserSystem) (time : Nat → Nat) :
    Trace BelugaState :=
  fun k => (networkTraceWithPull system time k).base

/-- Generic structural lemma (template from `golden_roundTermination`):
length of `eraseDups` dominates the cardinality of the toFinset. -/
private lemma length_eraseDups_ge_card_toFinset {α : Type*} [DecidableEq α] :
    ∀ (l : List α), List.length (List.eraseDups l) ≥ Finset.card (List.toFinset l) := by
  intro l
  induction' l using List.reverseRecOn with l x ih
  · rfl
  · simp +decide [List.eraseDups_append]
    by_cases h : x ∈ l.toFinset <;> simp_all +decide [List.removeAll]
    exact Nat.lt_succ_of_le ‹_›

/-- Helper: under the propose-op block-shape invariant + author-bound,
`authorOfDigest ops r (digest system r vid_p) = some vid_p` whenever
there's a propose op for `vid_p` in `ops`. The find? returns SOME
matching op; by the invariant + digest injectivity, that op's author
must be `vid_p`. -/
private lemma authorOfDigest_of_propose
    (system : BlockSynchroniserSystem) (ops : List ValidatorOperation)
    (vid_p : ValidatorId) (r : Round)
    (h_v_bound : vid_p < system.n + 1)
    (h_inv : ∀ vid B' r', ValidatorOperation.block_propose vid B' r' ∈ ops →
              B'.author = vid ∧ B'.r = r' ∧ B'.d = digest system r' vid)
    (h_authors_bound : ∀ vid B' r', ValidatorOperation.block_propose vid B' r' ∈ ops →
                         vid < system.n + 1)
    (B : Block)
    (h_op : ValidatorOperation.block_propose vid_p B r ∈ ops) :
    authorOfDigest ops r (digest system r vid_p) = some vid_p := by
  unfold authorOfDigest
  obtain ⟨_, _, h_d_eq⟩ := h_inv vid_p B r h_op
  have h_witness_match :
      (match ValidatorOperation.block_propose vid_p B r with
       | .block_propose _ block r' => block.d == digest system r vid_p && r' == r
       | _ => false) = true := by simp [h_d_eq]
  cases h_find : ops.find? (fun op =>
      match op with
      | .block_propose _ block r' => block.d == digest system r vid_p && r' == r
      | _ => false) with
  | none =>
    rw [List.find?_eq_none] at h_find
    exact absurd h_witness_match (h_find _ h_op)
  | some op_found =>
    have h_op_found_mem : op_found ∈ ops := List.mem_of_find?_eq_some h_find
    have h_op_found_pred := List.find?_some h_find
    cases op_found with
    | block_propose v_f B_f r_f =>
      rw [Bool.and_eq_true] at h_op_found_pred
      obtain ⟨h_d_f, _⟩ := h_op_found_pred
      rw [beq_iff_eq] at h_d_f
      obtain ⟨_, _, h_d_inv⟩ := h_inv v_f B_f r_f h_op_found_mem
      have h_v_f_bound := h_authors_bound v_f B_f r_f h_op_found_mem
      have h_d_combine : digest system r_f v_f = digest system r vid_p := by
        rw [← h_d_inv]; exact h_d_f
      have ⟨_, hv_eq⟩ :=
        digest_injective system r_f r v_f vid_p h_v_f_bound h_v_bound h_d_combine
      change ((List.find? (fun op =>
          match op with
          | .block_propose _ block r' => block.d == digest system r vid_p && r' == r
          | _ => false) ops).bind (fun op =>
          match op with
          | .block_propose author _ _ => some author
          | _ => none)) = some vid_p
      rw [h_find]
      exact congrArg some hv_eq
    | block_accept _ _ => exact absurd h_op_found_pred (by simp)
    | block_store _ _ => exact absurd h_op_found_pred (by simp)

/-! ## Honest-list bridging helpers -/

/-- The list `(system.validators.filter (·.2)).map Prod.fst` has
nodup IDs. -/
private lemma honestList_nodup (system : BlockSynchroniserSystem) :
    ((system.validators.filter (fun p => p.2 = true)).map Prod.fst).Nodup := by
  have h_v_nodup : (system.validators.map Prod.fst).Nodup := system.validatorsNodup
  have h_sub : (system.validators.filter (fun p => p.2 = true)).map Prod.fst |>.Sublist
        (system.validators.map Prod.fst) :=
    List.Sublist.map Prod.fst List.filter_sublist
  exact h_v_nodup.sublist h_sub

/-- Generic helper: in a list with nodup IDs, `find?` on an ID
returns the matching pair. -/
private lemma find_of_mem_nodup_id_eq {α β : Type*} [DecidableEq α]
    (l : List (α × β)) (a : α) (b : β)
    (h_mem : (a, b) ∈ l)
    (h_nodup : (l.map Prod.fst).Nodup) :
    l.find? (fun q => q.1 = a) = some (a, b) := by
  induction l with
  | nil => simp at h_mem
  | cons hd tl ih =>
    rw [List.find?_cons]
    rw [List.mem_cons] at h_mem
    rw [List.map_cons] at h_nodup
    rcases h_mem with h_eq | h_in
    · subst h_eq; simp
    · by_cases h_match : hd.1 = a
      · have h_a_in_tl : a ∈ tl.map Prod.fst :=
          List.mem_map.mpr ⟨(a, b), h_in, rfl⟩
        rw [← h_match] at h_a_in_tl
        exact absurd h_a_in_tl h_nodup.notMem
      · simp [h_match]
        exact ih h_in h_nodup.of_cons

/-- Each member of `honestList` is honest. -/
private lemma honestList_all_honest (system : BlockSynchroniserSystem)
    (p : ValidatorId)
    (hp : p ∈ (system.validators.filter (fun q => q.2 = true)).map Prod.fst) :
    isHonestValidator system p = true := by
  rw [List.mem_map] at hp
  obtain ⟨q, h_q_in, h_q_eq⟩ := hp
  rw [List.mem_filter] at h_q_in
  obtain ⟨h_q_in_v, h_q_honest⟩ := h_q_in
  have h_q_pair : q = (p, true) := by
    cases q with
    | mk q1 q2 =>
      simp at h_q_eq h_q_honest
      subst h_q_eq; subst h_q_honest; rfl
  rw [h_q_pair] at h_q_in_v
  unfold isHonestValidator BlockSynchroniserSystem.isHonest
  rw [find_of_mem_nodup_id_eq system.validators p true h_q_in_v system.validatorsNodup]

/-! ## Main theorem: `network_eventualRoundAcceptance` -/

/-- Under the with-pull primitives, `networkBelugaTraceWithPull`
satisfies `EventualRoundAcceptance`, so T4's `EventualRoundAcceptance`
hypothesis becomes a derived fact rather than an axiom. -/
theorem network_eventualRoundAcceptance
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_time_unbounded : ∀ T, ∃ k, time k ≥ T)
    (h_delivery : NetworkDeliveryWithPull system time)
    (h_scheduling : TimeoutAdvanceWithPull system time)
    (h_spread : BoundedRoundSpread_networkTraceWithPull system time)
    (h_accept : AcceptScheduling system time) :
    EventualRoundAcceptance system (networkBelugaTraceWithPull system time) := by
  intro round vid h_vid_honest_prop
  have h_vid_honest : isHonestValidator system vid = true := h_vid_honest_prop
  -- Step 1: post-GST step.
  obtain ⟨k_gst, h_k_gst⟩ : ∃ k, time k ≥ system.GST := h_time_unbounded system.GST
  -- Step 2: bring all honest to currentRound ≥ round + 1 by some k_R.
  obtain ⟨k_R, _, _, h_all_at_R⟩ :=
    network_all_honest_eventually_at_roundWithPull system time h_mono h_delivery
      h_scheduling h_spread vid h_vid_honest k_gst h_k_gst (round + 1)
  -- The honest validator ID list.
  set honestList : List ValidatorId :=
    (system.validators.filter (fun p => p.2 = true)).map Prod.fst with h_honestList_def
  -- Step 3: iterate to get k_acc where vid accepts every honest digest.
  obtain ⟨k_acc, h_acc⟩ :=
    all_honest_in_list_eventually_accepted system time h_mono h_time_unbounded
      h_delivery h_scheduling h_spread h_accept round vid h_vid_honest
      honestList (fun p hp => honestList_all_honest system p hp)
  -- Step 4: take k_final = max k_acc k_R; both conditions lift by monotonicity.
  set k_final := max k_acc k_R with h_k_final_def
  refine ⟨k_final, ?_⟩
  -- Lift acceptance to k_final.
  have h_acc_final : ∀ p ∈ honestList,
      hasAcceptedDigest (networkTraceWithPull system time k_final).base vid
        (digest system round p) = true := by
    intro p hp
    exact network_hasAcceptedDigest_monotone_withPull system time vid (digest system round p)
      k_acc k_final (le_max_left _ _) (h_acc p hp)
  -- At k_R, every honest has proposed for round; lift to k_final via monotonicity.
  have h_propose_final : ∀ p ∈ honestList,
      hasProposedFor (networkTraceWithPull system time k_final).base p round = true := by
    intro p hp
    have h_p_honest := honestList_all_honest system p hp
    obtain ⟨bv_p, h_bv_p, h_bv_p_round⟩ := h_all_at_R p h_p_honest
    have h_proposed_at_R :
        hasProposedFor (networkTraceWithPull system time k_R).base p round = true :=
      network_proposed_for_lt_currentRoundWithPull system time k_R p bv_p h_bv_p round
        h_bv_p_round
    exact network_hasProposedFor_monotoneWithPull system time p round k_R k_final
      (le_max_right _ _) h_proposed_at_R
  -- For each honest p, get the propose op witness.
  have h_propose_op_final : ∀ p ∈ honestList, ∃ B,
      ValidatorOperation.block_propose p B round ∈
        (networkTraceWithPull system time k_final).base.emittedOperations := by
    intro p hp
    exact hasProposedFor_implies_propose_op _ p round (h_propose_final p hp)
  -- Set up acceptedAuthors at k_final.
  set ops : List ValidatorOperation := opsAt (networkBelugaTraceWithPull system time) k_final
    with h_ops_def
  set acceptedAuthors_pre : List ValidatorId :=
    ops.filterMap (fun op =>
      match op with
      | .block_accept vid' d =>
        if vid' = vid then authorOfDigest ops round d else none
      | _ => none) with h_acceptedAuthors_pre_def
  -- Show honestList.toFinset ⊆ acceptedAuthors_pre.toFinset.
  have h_subset : honestList.toFinset ⊆ acceptedAuthors_pre.toFinset := by
    intro p hp
    rw [List.mem_toFinset] at hp ⊢
    have h_p_honest := honestList_all_honest system p hp
    -- Get the accept op.
    have h_acc_p := h_acc_final p hp
    rw [hasAcceptedDigest_iff_HasAccepted] at h_acc_p
    have h_accept_op : ValidatorOperation.block_accept vid (digest system round p) ∈ ops :=
      h_acc_p
    -- Get the propose op witness.
    obtain ⟨B, h_propose_op⟩ := h_propose_op_final p hp
    -- Apply authorOfDigest_of_propose.
    have h_inv := network_propose_op_invariant_traceWithPull system time k_final
    have h_authors_bound : ∀ vid B' r', .block_propose vid B' r' ∈ ops →
        vid < system.n + 1 := fun v B' r' h =>
      network_propose_op_author_bounded_traceWithPull system time k_final v B' r' h
    have h_inv' : ∀ vid B' r', .block_propose vid B' r' ∈ ops →
        B'.author = vid ∧ B'.r = r' ∧ B'.d = digest system r' vid := fun v B' r' h => by
      exact (h_inv v B' r' h).imp_right (·.imp_right (·.left))
    have h_v_bound : p < system.n + 1 :=
      network_propose_op_author_bounded_traceWithPull system time k_final p B round h_propose_op
    have h_aod : authorOfDigest ops round (digest system round p) = some p :=
      authorOfDigest_of_propose system ops p round h_v_bound h_inv' h_authors_bound B
        h_propose_op
    -- Now show p ∈ acceptedAuthors_pre via filterMap.
    rw [h_acceptedAuthors_pre_def, List.mem_filterMap]
    refine ⟨ValidatorOperation.block_accept vid (digest system round p), h_accept_op, ?_⟩
    simp [h_aod]
  -- honestList.toFinset has card ≥ 2f+1.
  have h_honestList_card : honestList.toFinset.card ≥ 2 * system.f + 1 := by
    rw [List.toFinset_card_of_nodup (honestList_nodup system)]
    show ((system.validators.filter (fun p => p.2 = true)).map Prod.fst).length ≥ 2 * system.f + 1
    rw [List.length_map]
    exact system.honestBound
  -- Combine: 2f+1 ≤ honestList.toFinset.card ≤ acceptedAuthors_pre.toFinset.card
  --              ≤ acceptedAuthors_pre.eraseDups.length.
  have h_card_le : acceptedAuthors_pre.toFinset.card ≥ 2 * system.f + 1 :=
    le_trans h_honestList_card (Finset.card_mono h_subset)
  exact le_trans h_card_le (length_eraseDups_ge_card_toFinset acceptedAuthors_pre)

/-- **Theorem 4 (paper §5).** Network-trace formulation, with the
`EventualRoundAcceptance` derived from the with-pull primitives. -/
theorem network_theorem4_round_termination_proved
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_time_unbounded : ∀ T, ∃ k, time k ≥ T)
    (h_delivery : NetworkDeliveryWithPull system time)
    (h_scheduling : TimeoutAdvanceWithPull system time)
    (h_spread : BoundedRoundSpread_networkTraceWithPull system time)
    (h_accept : AcceptScheduling system time) :
    Properties.RoundTermination system (networkBelugaTraceWithPull system time) := by
  intro round vid h_honest
  exact network_eventualRoundAcceptance system time h_mono h_time_unbounded
    h_delivery h_scheduling h_spread h_accept round vid h_honest

/-! ## T1 (BlockAvailability) and T3 (RoundProgression) on `networkTraceWithPull` -/

/-- Helper: under nodup, find? on a system-registered honest validator returns
the honest pair. -/
private lemma network_isHonestValidator_of_mem
    (system : BlockSynchroniserSystem) (vid : ValidatorId)
    (h_mem : (vid, true) ∈ system.validators) :
    isHonestValidator system vid = true := by
  unfold isHonestValidator BlockSynchroniserSystem.isHonest
  have h_find : system.validators.find? (fun p => p.1 == vid) = some (vid, true) :=
    find?_of_mem_nodup _ vid true h_mem system.validatorsNodup
  have h_pred_eq :
      (fun (x : ValidatorId × Bool) => match x with | (vid_1, _) => decide (vid_1 = vid))
        = (fun p => p.1 == vid) := by
    funext p
    cases p
    show decide _ = (_ == _)
    rfl
  rw [h_pred_eq, h_find]

/-- emittedOperations monotonicity along `networkTraceWithPull`. -/
private lemma networkBelugaTraceWithPull_emittedOperations_monotone
    (system : BlockSynchroniserSystem) (time : Nat → Nat) (k₁ k₂ : Nat) (h_le : k₁ ≤ k₂) :
    ∀ op ∈ (networkTraceWithPull system time k₁).base.emittedOperations,
      op ∈ (networkTraceWithPull system time k₂).base.emittedOperations := by
  induction h_le with
  | refl => intro _ h; exact h
  | step _ ih =>
    intro op hop
    rename_i k_mid _
    have ih' := ih op hop
    show op ∈ (networkStepWithPull system (networkTraceWithPull system time k_mid)
                (time (k_mid + 1))).base.emittedOperations
    exact networkStepWithPull_emittedOperations_monotone system _ _ op ih'

/-- **Theorem 1 (paper §5), with-pull.** Mirror of T1 on
`networkTraceWithPull`. Same proof structure, threading the with-pull
helpers in place of their without-pull counterparts. -/
theorem network_theorem1_block_availability_withPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_time_unbounded : ∀ T, ∃ k, time k ≥ T)
    (h_delivery : NetworkDeliveryWithPull system time)
    (h_scheduling : TimeoutAdvanceWithPull system time)
    (h_spread : BoundedRoundSpread_networkTraceWithPull system time) :
    Properties.BlockAvailability system (networkBelugaTraceWithPull system time) := by
  intro k vid d h_honest h_acc
  obtain ⟨k_post, hk_post_le, hk_post_gst⟩ : ∃ k', k ≤ k' ∧ time k' ≥ system.GST := by
    obtain ⟨k', hk'⟩ := h_time_unbounded system.GST
    exact ⟨max k k', le_max_left _ _, le_trans hk' (h_mono _ _ (le_max_right _ _))⟩
  obtain ⟨bv_post, h_bv_post⟩ :=
    network_honest_validator_persistent_traceWithPull system time vid h_honest k_post
  set r := bv_post.currentRound with hr_def
  have h_persistent : ∀ vid k, isHonestValidator system vid = true →
      ∃ bv, (networkTraceWithPull system time k).base.getValidator vid = some bv :=
    fun vid k h => network_honest_validator_persistent_traceWithPull system time vid h k
  obtain ⟨k_target, hk_target_le, _, h_target_all⟩ :=
    schedulerFairness_holds_withPull system time h_mono
      h_delivery h_scheduling h_spread h_persistent
      k_post r hk_post_gst ⟨vid, bv_post, h_honest, h_bv_post, hr_def.symm⟩
  obtain ⟨bv_target, h_bv_target, hbv_target_rnd⟩ := h_target_all vid h_honest
  obtain ⟨k_a, bv_a, bv_a', hk_a_le, _, h_a, h_a', h_a_eq, h_a'_eq⟩ :=
    network_find_advance_stepWithPull system time vid r hk_target_le bv_post bv_target
      h_bv_post h_bv_target hr_def.symm hbv_target_rnd
  have h_nodup_a := networkTraceWithPull_validators_nodup system time k_a
  have h_advance : bv_a'.currentRound = bv_a.currentRound + 1 := by rw [h_a_eq, h_a'_eq]
  have h_a'_step :
      (networkStepWithPull system (networkTraceWithPull system time k_a) (time (k_a + 1))).base.getValidator vid
        = some bv_a' := h_a'
  have h_stored_gate :=
    networkStepWithPull_advance_implies_stored system (networkTraceWithPull system time k_a) (time (k_a + 1))
      vid bv_a bv_a' h_nodup_a h_a h_a'_step h_advance
  have h_acc_at_a : HasAccepted (networkTraceWithPull system time k_a).base vid d := by
    have h_le : k ≤ k_a := le_trans hk_post_le hk_a_le
    exact networkBelugaTraceWithPull_emittedOperations_monotone system time k k_a h_le _ h_acc
  have h_acc_bool :
      hasAcceptedDigest (networkTraceWithPull system time k_a).base vid d = true := by
    unfold hasAcceptedDigest
    rw [List.any_eq_true]
    exact ⟨_, h_acc_at_a, by simp +decide⟩
  obtain ⟨B, hB_mem, hB_d⟩ :=
    network_acceptedBlockExists_traceWithPull system time vid k_a d h_acc_at_a
  have h_acc_B :
      hasAcceptedDigest (networkTraceWithPull system time k_a).base vid B.d = true := by
    rw [hB_d]; exact h_acc_bool
  have h_sto_B :
      hasStoredDigest (networkTraceWithPull system time k_a).base vid B.d = true :=
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
    · show ValidatorOperation.block_store vid B' ∈
        (networkBelugaTraceWithPull system time k_a).emittedOperations
      rw [h_v] at hop_mem; exact hop_mem
    · rw [h_d]; exact hB_d
  | _ => simp at hop_match

/-- **Theorem 3 (paper §5), with-pull.** Mirror of T3 on
`networkTraceWithPull`. -/
theorem network_theorem3_round_progression_withPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_time_unbounded : ∀ T, ∃ k, time k ≥ T)
    (h_delivery : NetworkDeliveryWithPull system time)
    (h_scheduling : TimeoutAdvanceWithPull system time)
    (h_spread : BoundedRoundSpread_networkTraceWithPull system time) :
    Properties.RoundProgression system (networkBelugaTraceWithPull system time) := by
  intro round
  have hHonest := system.honestBound
  set honest_pairs := system.validators.filter (fun p => p.2 = true) with h_hp_def
  have h_hp_ne : honest_pairs ≠ [] := by
    intro h_e
    have : honest_pairs.length = 0 := by rw [h_e]; rfl
    omega
  set pair_w := honest_pairs.head h_hp_ne
  have h_pair_w_mem : pair_w ∈ honest_pairs := List.head_mem _
  have h_pw_filter := List.mem_filter.mp h_pair_w_mem
  have h_pw_in : pair_w ∈ system.validators := h_pw_filter.1
  have h_pw_true : pair_w.2 = true := by simpa using h_pw_filter.2
  set vid_w := pair_w.1 with hv_w_def
  have h_w_pair_eq : (vid_w, true) ∈ system.validators := by
    have h_eq : pair_w = (vid_w, true) := by
      apply Prod.ext
      · rfl
      · exact h_pw_true
    rw [← h_eq]; exact h_pw_in
  have h_w_honest : isHonestValidator system vid_w = true :=
    network_isHonestValidator_of_mem system vid_w h_w_pair_eq
  obtain ⟨k₀, h_k₀_gst⟩ := h_time_unbounded system.GST
  obtain ⟨k, _, _, h_all⟩ :=
    network_all_honest_eventually_at_roundWithPull system time h_mono
      h_delivery h_scheduling h_spread
      vid_w h_w_honest k₀ h_k₀_gst (round + 1)
  refine ⟨k, ?_⟩
  set honest_vids := honest_pairs.map Prod.fst with h_hv_def
  have h_hv_len : honest_vids.length ≥ 2 * system.f + 1 := by
    rw [h_hv_def, List.length_map]; exact hHonest
  have h_sys_nodup := system.validatorsNodup
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
      find?_of_mem_nodup _ x.1 x.2 hx_in h_sys_nodup
    have hy_find : system.validators.find? (fun z => z.1 == y.1) = some y :=
      find?_of_mem_nodup _ y.1 y.2 hy_in h_sys_nodup
    rw [h_eq] at hx_find
    rw [hx_find] at hy_find
    grind
  set proposers_raw := (opsAt (networkBelugaTraceWithPull system time) k).filterMap (fun op =>
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
      network_isHonestValidator_of_mem system vid h_vid_pair_in
    obtain ⟨bv, h_bv, h_bv_round⟩ := h_all vid h_vid_honest
    have h_round_lt : round < bv.currentRound := h_bv_round
    have h_prop := network_proposed_for_lt_currentRoundWithPull system time k vid bv h_bv round h_round_lt
    obtain ⟨B, h_op⟩ := hasProposedFor_implies_propose_op _ vid round h_prop
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
  have h_pr_ge : proposers_raw.eraseDups.length ≥ proposers_raw.toFinset.card :=
    length_eraseDups_ge_card_toFinset proposers_raw
  omega

/-! ## `EventualCausalAcceptance` via `Reaches` induction

The proof is structural: induction on the `Reaches` relation, with the
universal in-pool acceptance step factored into a single hypothesis. -/

/-- Modulo a universal in-pool acceptance hypothesis, the `Reaches`
induction closes `EventualCausalAcceptance` on `networkBelugaTraceWithPull`.
The hypothesis says: every honest validator eventually accepts every
block in the pool (post-GST). -/
theorem network_eventualCausalAcceptance_modulo_gap
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_time_unbounded : ∀ T, ∃ k, time k ≥ T)
    (h_in_pool_accept : ∀ k vid B,
      isHonestValidator system vid = true →
      time k ≥ system.GST →
      B ∈ (networkTraceWithPull system time k).base.blocks →
      ∃ k', k ≤ k' ∧
        hasAcceptedDigest (networkTraceWithPull system time k').base vid B.d = true) :
    EventualCausalAcceptance system (networkBelugaTraceWithPull system time) := by
  intro k vid d B h_vid_honest_prop h_acc h_get B' h_reach
  have h_vid_honest : isHonestValidator system vid = true := h_vid_honest_prop
  induction h_reach with
  | refl =>
    -- B' = B (unified by induction). vid has accepted d, and B.d = d.
    refine ⟨k, le_rfl, ?_⟩
    have h_d_eq : B.d = d := by
      unfold getBlockByDigest at h_get
      have h_b_pred := List.find?_some h_get
      simpa using h_b_pred
    rw [h_d_eq]; exact h_acc
  | step _ h_parent_isP =>
    rename_i b parent m h_ih
    -- IH: ∃ k', k ≤ k' ∧ HasAccepted (trace k') vid m.d.
    obtain ⟨k_m, hk_m_le, h_acc_m⟩ := h_ih
    -- parent is in pool at step k.
    have h_parent_in_pool_k : parent ∈ (networkTraceWithPull system time k).base.blocks :=
      h_parent_isP.2.1
    have h_parent_in_pool_km : parent ∈ (networkTraceWithPull system time k_m).base.blocks :=
      network_blocks_monotone_traceWithPull system time k k_m hk_m_le parent h_parent_in_pool_k
    obtain ⟨k_extra, h_k_extra_gst⟩ := h_time_unbounded system.GST
    let k_gst := max k_m k_extra
    have hk_gst_ge_m : k_m ≤ k_gst := le_max_left _ _
    have hk_gst_post_gst : time k_gst ≥ system.GST :=
      le_trans h_k_extra_gst (h_mono _ _ (le_max_right _ _))
    have h_parent_in_pool_kgst : parent ∈ (networkTraceWithPull system time k_gst).base.blocks :=
      network_blocks_monotone_traceWithPull system time k_m k_gst hk_gst_ge_m parent
        h_parent_in_pool_km
    obtain ⟨k_acc, hk_acc_ge, h_acc_parent⟩ :=
      h_in_pool_accept k_gst vid parent h_vid_honest hk_gst_post_gst h_parent_in_pool_kgst
    refine ⟨k_acc, ?_, ?_⟩
    · exact le_trans hk_m_le (le_trans hk_gst_ge_m hk_acc_ge)
    · rw [hasAcceptedDigest_iff_HasAccepted] at h_acc_parent
      exact h_acc_parent

/-! ## `EventualCausalAcceptance` as a derived theorem -/

/-- Under the with-pull primitives — including `NetworkInPoolDeliveryWithPull`
which captures paper §4.3's universal pull-channel delivery —
`networkBelugaTraceWithPull` satisfies `EventualCausalAcceptance`,
turning T2's hypothesis into a derived fact. Combined with
`network_eventualRoundAcceptance`, both `Eventual*` axioms become
theorems. -/
theorem network_eventualCausalAcceptance
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_time_unbounded : ∀ T, ∃ k, time k ≥ T)
    (h_in_pool_delivery : NetworkInPoolDeliveryWithPull system time)
    (h_accept : AcceptScheduling system time) :
    EventualCausalAcceptance system (networkBelugaTraceWithPull system time) :=
  network_eventualCausalAcceptance_modulo_gap system time h_mono h_time_unbounded
    (fun k vid B h_v h_g h_p =>
      network_in_pool_eventually_accepted_withPull system time h_mono
        h_in_pool_delivery h_accept k vid B h_v h_g h_p)

/-! ## With-pull T2 (CausalAvailability) wrapper -/

/-- **Theorem 2 (paper §5), with-pull.** T2 expressed against
`networkTraceWithPull`, taking `EventualCausalAcceptance` as a
hypothesis. The hypothesis is discharged by
`network_eventualCausalAcceptance` to obtain the axiom-free corollary. -/
theorem network_theorem2_causal_availability_withPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_eventual : EventualCausalAcceptance system (networkBelugaTraceWithPull system time)) :
    Properties.CausalAvailability system (networkBelugaTraceWithPull system time) := by
  intro k vid d B h_honest h_acc h_get B' h_reach
  exact h_eventual k vid d B h_honest h_acc h_get B' h_reach

/-! ## Unified with-pull corollary: Beluga-with-pull is a block synchronizer -/

/-- **§5 corollary (axiom-free).** Under the with-pull primitives,
`networkBelugaTraceWithPull` satisfies all four block-synchronizer
properties. All four theorems (T1/T2/T3/T4) are fully derived; no
`Eventual*` axioms remain. -/
theorem networkTraceWithPull_isBlockSynchronizer
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_time_unbounded : ∀ T, ∃ k, time k ≥ T)
    (h_delivery : NetworkDeliveryWithPull system time)
    (h_scheduling : TimeoutAdvanceWithPull system time)
    (h_spread : BoundedRoundSpread_networkTraceWithPull system time)
    (h_accept : AcceptScheduling system time)
    (h_in_pool_delivery : NetworkInPoolDeliveryWithPull system time) :
    Properties.BlockSynchronizer system (networkBelugaTraceWithPull system time) :=
  ⟨network_theorem3_round_progression_withPull system time h_mono h_time_unbounded
     h_delivery h_scheduling h_spread,
   network_theorem4_round_termination_proved system time h_mono h_time_unbounded
     h_delivery h_scheduling h_spread h_accept,
   network_theorem1_block_availability_withPull system time h_mono h_time_unbounded
     h_delivery h_scheduling h_spread,
   network_theorem2_causal_availability_withPull system time
     (network_eventualCausalAcceptance system time h_mono h_time_unbounded
       h_in_pool_delivery h_accept)⟩


/-! ## §5 headline -/

/-- **§5 headline theorem.** Under `BelugaWithPullFairness`, the
network-aware Beluga trace satisfies all four block-synchronizer
properties (T1: BlockAvailability, T2: CausalAvailability, T3:
RoundProgression, T4: RoundTermination). All four are fully derived;
no `Eventual*` axioms remain. -/
theorem beluga_isBlockSynchronizer
    {system : BlockSynchroniserSystem} {time : Nat → Nat}
    (h : BelugaWithPullFairness system time) :
    Properties.BlockSynchronizer system (networkBelugaTraceWithPull system time) :=
  networkTraceWithPull_isBlockSynchronizer system time
    h.timeMonotone h.timeUnbounded h.networkDelivery h.timeoutAdvance
    h.boundedRoundSpread h.acceptScheduling h.inPoolDelivery

end Network

end Beluga
end BlockSynchroniser
