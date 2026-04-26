/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Beluga-specific state (paper §4.1–§4.3).
-/
import BlockSynchroniser.Block
import BlockSynchroniser.Validator
import BlockSynchroniser.Operations
import BlockSynchroniser.System
import BlockSynchroniser.State

namespace BlockSynchroniser
namespace Beluga

/--
A reputation table `TR_i[]` (paper §4.2): a mapping from validator id to
score. Initialized to all zeros (Figure 8). We model it as an association
list — adequate for finite `n` and avoids needing a `DecidableEq` /
`Finmap` import for now.
-/
abbrev ReputationTable := List (ValidatorId × Nat)

namespace ReputationTable

/-- `lookup rt vid` returns `vid`'s score in `rt` (defaulting to `0`). -/
def lookup (rt : ReputationTable) (vid : ValidatorId) : Nat :=
  match rt.find? (fun (id, _) => id == vid) with
  | some (_, s) => s
  | none => 0

/-- `set rt vid s` updates `vid`'s entry in `rt` to score `s`, preserving the
order of other entries. If `vid` is absent, prepends a new entry. -/
def set (rt : ReputationTable) (vid : ValidatorId) (s : Nat) : ReputationTable :=
  if rt.any (fun (id, _) => id == vid) then
    rt.map (fun (id, s') => if id == vid then (id, s) else (id, s'))
  else
    (vid, s) :: rt

/-- `incr rt vid` adds 1 to `vid`'s score in `rt`. -/
def incr (rt : ReputationTable) (vid : ValidatorId) : ReputationTable :=
  set rt vid (lookup rt vid + 1)

/-- `decrBy rt vid n` subtracts `n` from `vid`'s score (saturating at 0). -/
def decrBy (rt : ReputationTable) (vid : ValidatorId) (n : Nat) : ReputationTable :=
  set rt vid (lookup rt vid - n)

/-- The initial reputation table for a system: every validator at score 0. -/
def init (system : BlockSynchroniserSystem) : ReputationTable :=
  system.validators.map (fun (vid, _) => (vid, 0))

end ReputationTable

/--
A Beluga validator's local state.

Extends the abstract `Validator` (which tracks accepted/stored block digests)
with the Beluga-specific fields from paper §4.2–§4.3:

* `reputation` — the validator's local `TR_i[]` table.
* `currentRound` — the round `v_i` is currently in.
* `pendingBlocks` — blocks `v_i` has received but not yet output `block_accept` for
  (e.g., waiting for missing causal history; see §4.3.1 ImPoA mechanism).
* `liveBulk` — the partition of pending blocks into live (paper §4.3.2 live
  module) and bulk (bulk module) for the hybrid pull strategy. `(live, bulk)`.
-/
structure BelugaValidator where
  acceptedBlocks : List BlockDigest := []
  storedBlocks   : List BlockDigest := []
  reputation     : ReputationTable  := []
  currentRound   : Round            := 0
  pendingBlocks  : List BlockDigest := []
  liveBulk       : List BlockDigest × List BlockDigest := ([], [])
  /-- Wall-clock at which the validator entered `currentRound`. Used by
  the per-round timeout `T_rd = 4Δ` (paper §4.2). Default `0` covers
  the initial state where every validator starts at round `0` at
  wall-clock `0`. The timeout fires at wall-clock
  `roundEntryTime + 4Δ`. -/
  roundEntryTime : Nat := 0
  deriving Repr, DecidableEq

/-- Project a `BelugaValidator` to the abstract `Validator` (drop Beluga
fields). Used when satisfying the `SystemState` typeclass. -/
def BelugaValidator.toValidator (bv : BelugaValidator) : Validator :=
  { acceptedBlocks := bv.acceptedBlocks
    storedBlocks   := bv.storedBlocks }

/--
The full Beluga system state.

Carries the per-validator local Beluga state, the global block pool, and the
monotone log of operations. The `SystemState BelugaState` instance erases the
Beluga-specific fields, so all theorems stated against the abstract
`SystemState` typeclass apply uniformly to Beluga states.
-/
structure BelugaState where
  validators        : List (ValidatorId × BelugaValidator) := []
  blocks            : List Block                            := []
  emittedOperations : List ValidatorOperation               := []
  deriving Repr

instance : SystemState BelugaState where
  validators        s := s.validators.map (fun (vid, bv) => (vid, bv.toValidator))
  blocks            s := s.blocks
  emittedOperations s := s.emittedOperations

/-- The initial Beluga state for a system: each registered validator gets an
empty local state with reputation table initialized to all zeros. -/
def BelugaState.init (system : BlockSynchroniserSystem) : BelugaState where
  validators := system.validators.map (fun (vid, _) =>
    (vid, { reputation := ReputationTable.init system : BelugaValidator }))
  blocks := []
  emittedOperations := []

/-- Lookup a validator's Beluga local state by id. -/
def BelugaState.getValidator (s : BelugaState) (vid : ValidatorId) :
    Option BelugaValidator :=
  s.validators.find? (fun (id, _) => id == vid) |>.map (·.2)

end Beluga
end BlockSynchroniser
