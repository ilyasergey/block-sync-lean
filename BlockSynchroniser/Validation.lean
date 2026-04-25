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
  (`n=4, f=1`) that satisfies all four properties non-trivially. Stated here;
  proofs deferred to Aristotle (or a future hand-proof pass) — see the
  `sorry`-blocks for `PROVIDED SOLUTION` sketches.

* **(B) Realizability.** For each property `P → ∃ Q`, a sibling lemma showing
  the antecedent `P` is reachable in *some* trace. If `P` is never satisfiable,
  the property is moot. Proved here (without `sorry`).

* **(C) Anti-witnesses.** Construct `emptyTrace` and show it fails at least
  one property — catches over-permissive definitions. Proved here (without
  `sorry`).
-/

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
  -- `opsAt emptyTrace k = []`, so the filterMap is `[]` and its length is 0.
  simp [opsAt, emptyTrace, emptyState, SystemState.emittedOperations] at hk

/-- The empty trace fails Round-Termination for any honest validator (here,
validator 0): no `block_accept` ever fires. -/
theorem not_roundTermination_emptyTrace :
    ¬ RoundTermination goldenSystem emptyTrace := by
  intro h
  have honest0 : isHonestValidator goldenSystem 0 = true := by decide
  obtain ⟨k, hk⟩ := h 0 0 honest0
  simp [opsAt, emptyTrace, emptyState, SystemState.emittedOperations] at hk

/-! ## (A) goldenTrace satisfaction (deferred)

`goldenTrace` is a concrete honest-synchronous trace where, in each round `r`,
all four validators propose, accept each others' round-`r` blocks, and store
them. The four `golden_*` theorems below state that `goldenTrace` satisfies
each Definition-1 property non-trivially. Proofs are deferred — see the
`PROVIDED SOLUTION` sketches above each `sorry`. -/

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

/-- **Definition 1.1 — Round-Progression** holds for `goldenTrace`.

PROVIDED SOLUTION
For an arbitrary round `r`, take `k := 36 * r + 4`. After 36*r operations the
trace has fully simulated rounds `0..r-1`; the next 4 operations are the four
round-`r` proposes by validators `0,1,2,3`. So `opsAt goldenTrace (36*r + 4)`
contains four distinct `block_propose _ _ r` operations from validators
`{0,1,2,3}`, hence the deduplicated list of round-`r` proposers has length
`4 ≥ 3 = 2f+1`. The proof unfolds `goldenTrace`, `gOpsThrough`, `gRoundOps`,
computes the prefix, and concludes with `decide` or list-membership lemmas.
-/
theorem golden_roundProgression : RoundProgression goldenSystem goldenTrace := by
  sorry

/-- **Definition 1.2 — Round-Termination** holds for `goldenTrace`.

PROVIDED SOLUTION
For arbitrary round `r` and honest `vid ∈ {0,1,2,3}`, take `k := 36 * (r+1)`.
At that step all 36 operations of round `r` are in the log, including the 4
`block_accept vid (r*4 + i)` operations for `i ∈ {0,1,2,3}`. The
`authorOfDigest` helper, when applied to digest `r*4 + i` and round `r`,
returns `some i` because the propose operation `block_propose i (gBlock r i) r`
is present and `(gBlock r i).d = r*4 + i`. So the deduplicated list of
authors of accepted round-`r` blocks is `[0,1,2,3]`, length `4 ≥ 3 = 2f+1`.
-/
theorem golden_roundTermination : RoundTermination goldenSystem goldenTrace := by
  sorry

/-- **Definition 1.3 — Block availability** holds for `goldenTrace`.

PROVIDED SOLUTION
Fix any step `k`, honest `vid`, and digest `d` with `HasAccepted (goldenTrace k) vid d`.
By construction, `block_accept vid d` appears in `gOpsThrough (k/36)`, so
`d = r*4 + i` for some `r ≤ k/36` and `i ∈ {0,1,2,3}`. The trace also emits
`block_store vid (gBlock r i)` later in round `r` (phase 3). Take `k' := k + 36`
(safely past round `r`'s store phase). At step `k'`, the operation log
contains `block_store vid (gBlock r i)`, and `(gBlock r i).d = r*4 + i = d`.
-/
theorem golden_blockAvailability : BlockAvailability goldenSystem goldenTrace := by
  sorry

/-- **Definition 1.4 — Causal availability** holds for `goldenTrace`.

PROVIDED SOLUTION
Fix `k vid d B` with `HasAccepted (goldenTrace k) vid d` and `getBlockByDigest
(goldenTrace k) d = some B`. The block `B = gBlock r i` for some `r,i`. The
parents of `B` (if `r > 0`) are the four round-`(r-1)` blocks; iterating, the
causal closure `Reaches state B B'` consists of `gBlock r' i'` for all
`(r', i') ≤ (r, _)`. By induction on `r' ≤ r`: at step `36*(r' + 1)` the trace
has emitted `block_accept vid (r' * 4 + i')` for every `i' ∈ {0,1,2,3}`. So
`vid` has accepted every causal ancestor's digest. Take `k' := max k (36*(r+1))`.
-/
theorem golden_causalAvailability : CausalAvailability goldenSystem goldenTrace := by
  sorry

/-- The headline non-vacuity result: there exists a trace satisfying all four
Definition-1 properties. Follows immediately from the four `golden_*` theorems. -/
theorem goldenTrace_isBlockSynchronizer :
    BlockSynchronizer goldenSystem goldenTrace :=
  ⟨golden_roundProgression, golden_roundTermination,
   golden_blockAvailability, golden_causalAvailability⟩

end Validation
end BlockSynchroniser
