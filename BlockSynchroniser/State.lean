/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.
-/
import BlockSynchroniser.Block
import BlockSynchroniser.Validator
import BlockSynchroniser.Operations

namespace BlockSynchroniser

/--
Abstract system state.

A type class so callers can plug in a richer state representation (e.g. one
that tracks reputation and admission control) without changing the abstract
properties stated in `Properties.lean`.

Three observers: the per-validator local views, the set of all blocks the
system knows about, and the monotone log of operations emitted so far.
-/
class SystemState (S : Type) where
  validators        : S → List (ValidatorId × Validator)
  blocks            : S → List Block
  emittedOperations : S → List ValidatorOperation

/-- The default concrete state — a triple of the three observer fields. -/
structure DefaultSystemState where
  validators        : List (ValidatorId × Validator)
  blocks            : List Block
  emittedOperations : List ValidatorOperation

instance : SystemState DefaultSystemState where
  validators        s := s.validators
  blocks            s := s.blocks
  emittedOperations s := s.emittedOperations

/-- Fetch a validator's local state by id, if registered. -/
def getValidatorById {S} [SystemState S] (state : S) (id : ValidatorId) : Option Validator :=
  (SystemState.validators state).find? (fun (vid, _) => vid = id) |>.map (·.2)

/-- Fetch a block by digest, if known to the state. -/
def getBlockByDigest {S} [SystemState S] (state : S) (digest : BlockDigest) : Option Block :=
  (SystemState.blocks state).find? (fun b => b.d = digest)

end BlockSynchroniser
