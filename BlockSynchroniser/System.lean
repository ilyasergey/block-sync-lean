/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.
-/
import Mathlib.Data.List.Basic
import BlockSynchroniser.Block

namespace BlockSynchroniser

/--
Block synchronizer system parameters (paper §2).

Models a partially-synchronous network: `n` validators, of which up to `f` are
Byzantine (with the standard quorum-intersection bound `n ≥ 3f + 1`); a global
stabilization time `GST` after which delivery latency is bounded by `Δ`; and a
minimum number of parents `k` per block.

`validators` is the static membership: a list of `(id, isHonest)` pairs. The
`isHonestValidator` / `isByzantineValidator` predicates dispatch on this list.
-/
structure BlockSynchroniserSystem where
  /-- Total number of validators. -/
  n : Nat
  /-- Maximum number of Byzantine validators tolerated. -/
  f : Nat
  /-- Minimum number of parents required per block. -/
  k : Nat
  /-- Global stabilization time: after this step, the network is synchronous. -/
  GST : Nat
  /-- Post-`GST` upper bound on message delivery latency. -/
  Δ : Nat
  /-- Static validator membership: `(id, isHonest)`. -/
  validators : List (ValidatorId × Bool)
  /-- Quorum-intersection precondition: `n ≥ 3f + 1`. -/
  honestMajority : n ≥ 3 * f + 1
  /-- Validator IDs are unique (Nodup form). -/
  validatorsNodup : (validators.map Prod.fst).Nodup
  /-- The `validators` list has length `n`. -/
  validatorCountCorrect : n = validators.length
  /-- Validator IDs are bounded by `n + 1` (paper §2 implicit; needed for
  `digest` injectivity). -/
  validIds : ∀ p ∈ validators, p.1 < n + 1
  /-- Byzantine count is bounded by `f`. Combined with `honestMajority` and
  `validatorCountCorrect`, gives the standard `honest ≥ 2f + 1` bound. -/
  byzantineBound : (validators.filter (fun p => !p.2)).length ≤ f
  deriving Repr

namespace BlockSynchroniserSystem

/-- True iff `id` is a registered Byzantine validator in `system`. -/
def isByzantine (system : BlockSynchroniserSystem) (id : ValidatorId) : Bool :=
  match system.validators.find? (fun (vid, _) => vid = id) with
  | some (_, isHonest) => !isHonest
  | none => false

/-- True iff `id` is a registered honest validator in `system`. -/
def isHonest (system : BlockSynchroniserSystem) (id : ValidatorId) : Bool :=
  match system.validators.find? (fun (vid, _) => vid = id) with
  | some (_, isHonest) => isHonest
  | none => false

/-- Honest validator count is at least `2 * f + 1`. Derived from
`honestMajority` (`n ≥ 3f+1`), `validatorCountCorrect` (`n = validators.length`),
and `byzantineBound` (Byzantine count ≤ f). -/
theorem honestBound (system : BlockSynchroniserSystem) :
    (system.validators.filter (fun p => p.2)).length ≥ 2 * system.f + 1 := by
  have h_partition := List.length_eq_length_filter_add (l := system.validators)
    (f := fun p : ValidatorId × Bool => p.2)
  have h_n := system.validatorCountCorrect
  have h_maj := system.honestMajority
  have h_byz := system.byzantineBound
  omega

end BlockSynchroniserSystem

/-- Top-level alias preserved for callers (matches the legacy name). -/
abbrev isHonestValidator := BlockSynchroniserSystem.isHonest

/-- Top-level alias preserved for callers (matches the legacy name). -/
abbrev isByzantineValidator := BlockSynchroniserSystem.isByzantine

end BlockSynchroniser
