/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

# Validation lemmas for Definition 1's four properties (paper §2.1).

**These are NOT paper theorems.** They are *internal sanity checks on our
formalization*: each one demonstrates that our Lean version of a property is
satisfiable (or, dually, falsifiable) by a specific concrete trace.

* The paper's Theorems 1–4 (§5) say "**Beluga the protocol** satisfies each of
  the four properties." Those will live in `BlockSynchroniser/Beluga/Theorems.lean`
  in Phase 5, and they are stated against `BelugaTrace`, not the hand-built
  `goldenTrace` here.
* Everything in *this* file is about catching definition bugs *before* we try
  to prove the paper theorems. If `goldenTrace` cannot be shown to satisfy
  `RoundProgression`, the formal version of `RoundProgression` is suspect.

See `formalization.md` (top-level) for the project-wide picture and the
distinction spelled out.

## Three lines of defense (in order of effort)

* **(A) goldenTrace satisfaction.** A concrete honest-synchronous trace
  (`n=4, f=1`) that satisfies all four properties non-trivially.

* **(B) Realizability.** For each property `P → ∃ Q`, a sibling lemma showing
  the antecedent `P` is reachable in *some* trace. If `P` is never satisfiable,
  the property is moot.

* **(C) Anti-witnesses.** Construct `emptyTrace` and show it fails at least
  one property — catches over-permissive definitions.
-/

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import BlockSynchroniser.System
import BlockSynchroniser.State
import BlockSynchroniser.Causal
import BlockSynchroniser.Trace
import BlockSynchroniser.Properties

namespace BlockSynchroniser
namespace Validation

open Properties

/-! ## A four-validator honest-synchronous system. -/

/-- The 4-validator, single-Byzantine-budget system used by every witness in
this file. All four validators are honest. `k = 0` so blocks need no parents,
keeping witnesses self-contained. -/
def goldenSystem : BlockSynchroniserSystem where
  n          := 4
  f          := 1
  k          := 0
  GST        := 0
  Δ          := 1
  validators := [(0, true), (1, true), (2, true), (3, true)]
  honestMajority      := by decide
  validatorIdsUnique  := by decide
  validatorCountCorrect := by decide

/-- A simple round-0 block proposed by validator `i`, with no parents. -/
def goldenBlock (i : ValidatorId) : Block :=
  { r := 0, author := i, d := i, parents := [], payload := [] }

/-! ## (B) Realizability witnesses

For each operation kind, a one-step trace whose initial state already contains
the relevant operation. Used to demonstrate the antecedents `HasProposed`,
`HasAccepted`, `HasStored` are reachable. -/

/-- A state holding a single `block_propose` operation. -/
def proposeState : DefaultSystemState where
  validators        := []
  blocks            := [goldenBlock 0]
  emittedOperations := [.block_propose 0 (goldenBlock 0) 0]

/-- The constant trace for the propose witness. -/
def proposeTrace : Trace DefaultSystemState := fun _ => proposeState

/-- A state holding a single `block_accept` operation by validator 0 for digest 0. -/
def acceptState : DefaultSystemState where
  validators        := []
  blocks            := [goldenBlock 0]
  emittedOperations := [.block_accept 0 0]

/-- The constant trace for the accept witness. -/
def acceptTrace : Trace DefaultSystemState := fun _ => acceptState

/-- A state holding a single `block_store` operation by validator 0. -/
def storeState : DefaultSystemState where
  validators        := []
  blocks            := [goldenBlock 0]
  emittedOperations := [.block_store 0 (goldenBlock 0)]

/-- The constant trace for the store witness. -/
def storeTrace : Trace DefaultSystemState := fun _ => storeState

theorem realizable_propose :
    ∃ (trace : Trace DefaultSystemState) (k : Nat) (vid : ValidatorId) (B : Block) (r : Round),
      HasProposed (trace k) vid B r := by
  refine ⟨proposeTrace, 0, 0, goldenBlock 0, 0, ?_⟩
  simp [HasProposed, Emitted, proposeTrace, proposeState, SystemState.emittedOperations]

theorem realizable_accept :
    ∃ (trace : Trace DefaultSystemState) (k : Nat) (vid : ValidatorId) (d : BlockDigest),
      HasAccepted (trace k) vid d := by
  refine ⟨acceptTrace, 0, 0, 0, ?_⟩
  simp [HasAccepted, Emitted, acceptTrace, acceptState, SystemState.emittedOperations]

theorem realizable_store :
    ∃ (trace : Trace DefaultSystemState) (k : Nat) (vid : ValidatorId) (B : Block),
      HasStored (trace k) vid B := by
  refine ⟨storeTrace, 0, 0, goldenBlock 0, ?_⟩
  simp [HasStored, Emitted, storeTrace, storeState, SystemState.emittedOperations]

/-! ## (C) Anti-witnesses

The empty trace must fail at least one Definition-1 property. Otherwise the
property under-specifies: even a system that does nothing satisfies it. -/

/-- A state with no validators, no blocks, and no emitted operations. -/
def emptyState : DefaultSystemState where
  validators        := []
  blocks            := []
  emittedOperations := []

/-- The constant trace whose every state is `emptyState`. No operation ever
fires; in particular no validator ever proposes. -/
def emptyTrace : Trace DefaultSystemState := fun _ => emptyState

/-- The empty trace fails Round-Progression: round 0 has zero proposers
(certainly fewer than `2f + 1 = 3`). -/
theorem not_roundProgression_emptyTrace :
    ¬ RoundProgression goldenSystem emptyTrace := by
  intro h
  obtain ⟨k, hk⟩ := h 0
  simp [opsAt, emptyTrace, emptyState, SystemState.emittedOperations] at hk

/-- The empty trace fails Round-Termination for any honest validator (here,
validator 0): no `block_accept` ever fires. -/
theorem not_roundTermination_emptyTrace :
    ¬ RoundTermination goldenSystem emptyTrace := by
  intro h
  have honest0 : isHonestValidator goldenSystem 0 = true := by decide
  obtain ⟨k, hk⟩ := h 0 0 honest0
  simp [opsAt, emptyTrace, emptyState, SystemState.emittedOperations] at hk

/-! ## (A) goldenTrace satisfaction

`goldenTrace` is a concrete honest-synchronous trace where, in each round `r`,
all four validators propose, accept each others' round-`r` blocks, and store
them. The four `golden_*` theorems below state that `goldenTrace` satisfies
each Definition-1 property non-trivially. -/

/-- The block proposed by validator `i` in round `r`. Digest is unique:
`r * 4 + i`. For `r = 0` parents is empty; for `r ≥ 1` parents are the four
round-`(r-1)` blocks. -/
def gBlock (r : Round) (i : ValidatorId) : Block :=
  { r       := r
    author  := i
    d       := r * 4 + i
    parents := if r = 0 then [] else (List.range 4).map (fun j => (r - 1) * 4 + j)
    payload := [] }

/-- All blocks produced through round `R` (inclusive). Used to populate the
state's `blocks` field at later steps. -/
def gBlocksThrough (R : Nat) : List Block :=
  (List.range (R + 1)).flatMap (fun r => (List.range 4).map (gBlock r))

/-- Per-round operation sequence: 4 proposes, then 16 accepts (each validator
accepts each block), then 16 stores. 36 ops per round. -/
def gRoundOps (r : Round) : List ValidatorOperation :=
  -- Phase 1: 4 propose ops
  ((List.range 4).map (fun i => ValidatorOperation.block_propose i (gBlock r i) r)) ++
  -- Phase 2: 16 accept ops (vid v accepts block i, for v,i ∈ {0,1,2,3})
  ((List.range 4).flatMap (fun v =>
    (List.range 4).map (fun i => ValidatorOperation.block_accept v (r * 4 + i)))) ++
  -- Phase 3: 16 store ops
  ((List.range 4).flatMap (fun v =>
    (List.range 4).map (fun i => ValidatorOperation.block_store v (gBlock r i))))

/-- All operations through round `R` (inclusive): rounds 0, 1, ..., R, in order. -/
def gOpsThrough (R : Nat) : List ValidatorOperation :=
  (List.range (R + 1)).flatMap gRoundOps

/-- The state at step `n` of `goldenTrace`. Blocks for rounds `0..n/36` are
present; the operation log contains the first `n` operations of the periodic
sequence (rounds `0, 1, 2, ...` concatenated). -/
def goldenStateAt (n : Nat) : DefaultSystemState where
  validators        := []
  blocks            := gBlocksThrough (n / 36)
  emittedOperations := (gOpsThrough (n / 36)).take n

/-- The honest-synchronous golden trace. -/
def goldenTrace : Trace DefaultSystemState := goldenStateAt

/-! ## Helper lemmas for golden trace proofs -/

-- proof: aristotle (project be7c0245)
theorem gRoundOps_length (r : Round) : (gRoundOps r).length = 36 := by
  -- The length of `List.range 4` is 4.
  simp [gRoundOps, List.length_range, List.length_map]

theorem gOpsThrough_length (R : Nat) : (gOpsThrough R).length = 36 * (R + 1) := by
  unfold gOpsThrough;
  simp +arith +decide [ mul_comm, gRoundOps_length ]

theorem gOpsThrough_succ (R : Nat) :
    gOpsThrough (R + 1) = gOpsThrough R ++ gRoundOps (R + 1) := by
  unfold gOpsThrough; simp +decide [ List.range_succ ]

theorem gOpsThrough_take_full (R : Nat) :
    (gOpsThrough R).take (36 * (R + 1)) = gOpsThrough R := by
  rw [List.take_of_length_le]
  exact le_of_eq (gOpsThrough_length R)

theorem goldenTrace_ops_at_full_round (r : Nat) :
    opsAt goldenTrace (36 * (r + 1)) = gOpsThrough r := by
  unfold opsAt goldenTrace goldenStateAt;
  norm_num [ Nat.mul_div_assoc ];
  rw [ gOpsThrough_succ, List.take_append_of_le_length ];
  · exact List.take_of_length_le ( by linarith [ gOpsThrough_length r ] );
  · rw [ gOpsThrough_length ]

theorem gRoundOps_propose_mem (r : Round) (i : Nat) (hi : i < 4) :
    ValidatorOperation.block_propose i (gBlock r i) r ∈ gRoundOps r := by
  interval_cases i <;> simp +decide [ gRoundOps ]

theorem gRoundOps_accept_mem (r : Round) (v i : Nat) (hv : v < 4) (hi : i < 4) :
    ValidatorOperation.block_accept v (r * 4 + i) ∈ gRoundOps r := by
  unfold gRoundOps;
  simp +decide [ hv, hi ]

theorem gRoundOps_store_mem (r : Round) (v i : Nat) (hv : v < 4) (hi : i < 4) :
    ValidatorOperation.block_store v (gBlock r i) ∈ gRoundOps r := by
  interval_cases v <;> interval_cases i <;> simp +decide [ gRoundOps ];
  all_goals exact ⟨ _, by decide, rfl ⟩ ;

theorem gRoundOps_mem_gOpsThrough (r R : Nat) (hr : r ≤ R) (op : ValidatorOperation)
    (hop : op ∈ gRoundOps r) : op ∈ gOpsThrough R := by
  exact List.mem_flatMap.mpr ⟨ r, List.mem_range.mpr ( by linarith ), hop ⟩

theorem propose_mem_gOpsThrough (r R : Nat) (hr : r ≤ R) (i : Nat) (hi : i < 4) :
    ValidatorOperation.block_propose i (gBlock r i) r ∈ gOpsThrough R :=
  gRoundOps_mem_gOpsThrough r R hr _ (gRoundOps_propose_mem r i hi)

theorem accept_mem_gOpsThrough (r R : Nat) (hr : r ≤ R) (v i : Nat)
    (hv : v < 4) (hi : i < 4) :
    ValidatorOperation.block_accept v (r * 4 + i) ∈ gOpsThrough R :=
  gRoundOps_mem_gOpsThrough r R hr _ (gRoundOps_accept_mem r v i hv hi)

theorem store_mem_gOpsThrough (r R : Nat) (hr : r ≤ R) (v i : Nat)
    (hv : v < 4) (hi : i < 4) :
    ValidatorOperation.block_store v (gBlock r i) ∈ gOpsThrough R :=
  gRoundOps_mem_gOpsThrough r R hr _ (gRoundOps_store_mem r v i hv hi)

theorem isHonest_goldenSystem_iff (vid : ValidatorId) :
    isHonestValidator goldenSystem vid = true ↔ vid < 4 := by
  rcases vid with ( _ | _ | _ | _ | vid ) <;> tauto

/-
**Definition 1.1 — Round-Progression** holds for `goldenTrace`.
-/
-- proof: aristotle (project be7c0245)
theorem golden_roundProgression : RoundProgression goldenSystem goldenTrace := by
  intro r;
  refine' ⟨ 36 * ( r + 1 ), _ ⟩;
  rw [ goldenTrace_ops_at_full_round ];
  unfold gOpsThrough;
  unfold gRoundOps; simp +decide [ List.range_succ ] ;
  rw [ List.filterMap_flatMap ];
  simp +decide [ List.filterMap ];
  rw [ List.flatMap_congr ];
  rotate_right;
  use fun x => [];
  · induction r <;> simp_all +decide [ List.range_succ ];
  · intro x hx; split_ifs <;> simp_all +decide ;

/-
**Definition 1.2 — Round-Termination** holds for `goldenTrace`.
-/
-- proof: aristotle (project be7c0245)
theorem golden_roundTermination : RoundTermination goldenSystem goldenTrace := by
  -- For any round r and honest validator vid, we can choose k = 36 * (r + 1).
  intro r vid hvid
  use 36 * (r + 1);
  -- By definition of `goldenTrace`, we know that `opsAt goldenTrace (36 * (r + 1))` contains all proposers for round `r`.
  have h_ops : opsAt goldenTrace (36 * (r + 1)) = gOpsThrough r := by
    exact goldenTrace_ops_at_full_round r;
  -- By definition of `gOpsThrough`, we know that `gOpsThrough r` contains all proposers for round `r`.
  have h_proposers : ∀ i < 4, ValidatorOperation.block_accept vid (r * 4 + i) ∈ gOpsThrough r := by
    exact fun i hi => accept_mem_gOpsThrough r r le_rfl vid i ( by simpa [ isHonest_goldenSystem_iff ] using hvid ) hi;
  have h_acceptedAuthors : List.toFinset (List.filterMap (fun op => match op with | .block_accept vid' d => if vid' = vid then authorOfDigest (gOpsThrough r) r d else none | _ => none) (gOpsThrough r)) ⊇ {0, 1, 2, 3} := by
    have h_acceptedAuthors : ∀ i < 4, authorOfDigest (gOpsThrough r) r (r * 4 + i) = some i := by
      intros i hi
      have h_propose : ValidatorOperation.block_propose i (gBlock r i) r ∈ gOpsThrough r := by
        exact propose_mem_gOpsThrough r r le_rfl i hi;
      have h_unique_propose : ∀ op ∈ gOpsThrough r, op = ValidatorOperation.block_propose i (gBlock r i) r ∨ ¬(match op with | .block_propose _ block r' => block.d == r * 4 + i && r' == r | _ => false) := by
        intros op hop;
        contrapose! hop;
        rcases op with ( _ | _ | _ ) <;> simp +decide at hop ⊢;
        unfold gOpsThrough at *; simp_all +decide [ List.mem_flatMap ] ;
        unfold gRoundOps at *; simp_all +decide [ List.mem_flatMap ] ;
        unfold gBlock at *; aesop;
      have h_unique_propose : List.find? (fun op => match op with | .block_propose _ block r' => block.d == r * 4 + i && r' == r | _ => false) (gOpsThrough r) = some (ValidatorOperation.block_propose i (gBlock r i) r) := by
        have h_unique_propose : ∀ {l : List ValidatorOperation}, ValidatorOperation.block_propose i (gBlock r i) r ∈ l → (∀ op ∈ l, op = ValidatorOperation.block_propose i (gBlock r i) r ∨ ¬(match op with | .block_propose _ block r' => block.d == r * 4 + i && r' == r | _ => false)) → List.find? (fun op => match op with | .block_propose _ block r' => block.d == r * 4 + i && r' == r | _ => false) l = some (ValidatorOperation.block_propose i (gBlock r i) r) := by
          intros l hl hl_unique;
          induction' l with op l ih;
          · contradiction;
          · by_cases h : op = ValidatorOperation.block_propose i ( gBlock r i ) r <;> simp +decide [ h ] at hl hl_unique ⊢;
            · exact Or.inl rfl;
            · exact ⟨ by
                cases op <;> simp +decide;
                exact fun h₁ h₂ => hl_unique.1 ⟨ h₁, h₂ ⟩, ih ( hl.resolve_left ( Ne.symm h ) ) ( fun op hop => by
                convert hl_unique.2 op hop using 1;
                cases op <;> simp +decide [ and_comm ] ) ⟩;
        exact h_unique_propose h_propose ‹_›;
      exact Option.bind_eq_some_iff.mpr ⟨ _, h_unique_propose, rfl ⟩;
    intro x hx;
    simp +zetaDelta at *;
    use ValidatorOperation.block_accept vid (r * 4 + x);
    grind;
  have h_acceptedAuthors_length : List.length (List.eraseDups (List.filterMap (fun op => match op with | .block_accept vid' d => if vid' = vid then authorOfDigest (gOpsThrough r) r d else none | _ => none) (gOpsThrough r))) ≥ Finset.card (List.toFinset (List.filterMap (fun op => match op with | .block_accept vid' d => if vid' = vid then authorOfDigest (gOpsThrough r) r d else none | _ => none) (gOpsThrough r))) := by
    have h_acceptedAuthors_length : ∀ (l : List ValidatorId), List.length (List.eraseDups l) ≥ Finset.card (List.toFinset l) := by
      intro l;
      induction' l using List.reverseRecOn with l ih;
      · rfl;
      · simp +decide [ List.eraseDups_append ];
        by_cases h : ih ∈ l.toFinset <;> simp_all +decide [ List.removeAll ];
        exact Nat.lt_succ_of_le ‹_›;
    exact h_acceptedAuthors_length _;
  exact h_ops.symm ▸ h_acceptedAuthors_length.trans' ( le_trans ( by decide ) ( Finset.card_mono h_acceptedAuthors ) )

/-
**Definition 1.3 — Block availability** holds for `goldenTrace`.
-/
-- proof: aristotle (project be7c0245)
theorem golden_blockAvailability : BlockAvailability goldenSystem goldenTrace := by
  intro k vid d hvid hacc
  obtain ⟨r, i, hr, hi, hd⟩ : ∃ r i, r ≤ k / 36 ∧ i < 4 ∧ d = r * 4 + i := by
    -- By definition of `HasAccepted`, we know that `block_accept vid d` is in the operation log of `goldenTrace k`.
    obtain ⟨op, hop⟩ : ∃ op ∈ (gOpsThrough (k / 36)).take k, op = .block_accept vid d := by
      unfold HasAccepted at hacc; aesop;
    -- By definition of `gOpsThrough`, we know that `op` is in `gRoundOps r` for some `r ≤ k / 36`.
    obtain ⟨r, hr⟩ : ∃ r ≤ k / 36, op ∈ gRoundOps r := by
      have h_op_in_gRoundOps : op ∈ gOpsThrough (k / 36) := by
        exact List.mem_of_mem_take hop.1;
      unfold gOpsThrough at h_op_in_gRoundOps; aesop;
    unfold gRoundOps at hr; simp_all +decide [ List.mem_append, List.mem_map ] ;
    exact ⟨ r, hr.1, by obtain ⟨ x, hx, rfl ⟩ := hr.2.2; exact ⟨ x, hx, rfl ⟩ ⟩;
  refine' ⟨ 36 * ( k / 36 + 1 ), _, _ ⟩;
  · omega;
  · refine' ⟨ gBlock r i, _, _ ⟩;
    · have h_store : ValidatorOperation.block_store vid (gBlock r i) ∈ gOpsThrough (k / 36) := by
        apply store_mem_gOpsThrough r (k / 36) hr vid i (by
        exact isHonest_goldenSystem_iff vid |>.1 hvid) hi;
      convert List.mem_of_mem_take _;
      exact 36 * ( k / 36 + 1 );
      grind +suggestions;
    · aesop

/-
**Definition 1.4 — Causal availability** holds for `goldenTrace`.
-/
-- proof: aristotle (project be7c0245)
theorem golden_causalAvailability : CausalAvailability goldenSystem goldenTrace := by
  intro k vid d B h_honest h_accept h_block B' h_reaches;
  -- By definition of `goldenTrace`, we know that `B'` is of the form `gBlock r' i'` for some `r' ≤ k/36` and `i' < 4`.
  obtain ⟨r', i', hr', hi'⟩ : ∃ r' i', r' ≤ k / 36 ∧ i' < 4 ∧ B' = gBlock r' i' := by
    have hB'_form : B' ∈ (goldenTrace k).blocks := by
      have hB'_in_state : ∀ {B B' : Block}, Reaches (goldenTrace k) B B' → B ∈ (goldenTrace k).blocks → B' ∈ (goldenTrace k).blocks := by
        intros B B' h_reaches hB_in_state; induction h_reaches; aesop;
        unfold isParent at *; aesop;
      apply hB'_in_state h_reaches;
      exact List.mem_of_find?_eq_some h_block;
    unfold goldenTrace at hB'_form; simp_all +decide ;
    grind +locals;
  refine' ⟨ 36 * ( k / 36 + 1 ), _, _ ⟩;
  · omega;
  · refine' List.mem_of_mem_take _;
    exact 36 * ( k / 36 + 1 );
    convert accept_mem_gOpsThrough r' ( k / 36 ) hr' vid i' _ hi'.1 using 1;
    · -- By definition of `goldenTrace`, the emitted operations at step `36 * (k / 36 + 1)` are exactly `gOpsThrough (k / 36)`.
      have h_emitted : SystemState.emittedOperations (goldenTrace (36 * (k / 36 + 1))) = gOpsThrough (k / 36) := by
        convert goldenTrace_ops_at_full_round ( k / 36 ) using 1;
      rw [ h_emitted, gOpsThrough_take_full ];
    · aesop;
    · exact (isHonest_goldenSystem_iff vid).mp h_honest

/-- The headline non-vacuity result: there exists a trace satisfying all four
Definition-1 properties. Follows immediately from the four `golden_*` theorems. -/
theorem goldenTrace_isBlockSynchronizer :
    BlockSynchronizer goldenSystem goldenTrace :=
  ⟨golden_roundProgression, golden_roundTermination,
   golden_blockAvailability, golden_causalAvailability⟩

end Validation
end BlockSynchroniser