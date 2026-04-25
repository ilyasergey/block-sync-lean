/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.
-/
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
  /-- Validator IDs are unique. -/
  validatorIdsUnique :
    let validatorIds := validators.map (·.1)
    validatorIds.eraseDups.length = validatorIds.length
  /-- The `validators` list has length `n`. -/
  validatorCountCorrect : n = validators.length
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

end BlockSynchroniserSystem

/-- Top-level alias preserved for callers (matches the legacy name). -/
abbrev isHonestValidator := BlockSynchroniserSystem.isHonest

/-- Top-level alias preserved for callers (matches the legacy name). -/
abbrev isByzantineValidator := BlockSynchroniserSystem.isByzantine

end BlockSynchroniser
