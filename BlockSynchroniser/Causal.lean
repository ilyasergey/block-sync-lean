/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.
-/
import BlockSynchroniser.Block
import BlockSynchroniser.State

namespace BlockSynchroniser

/--
Direct parent relation (paper §2.1): `parent` is a parent of `child` if its
digest appears in `child.parents` and both blocks are recorded in the state.
-/
def isParent {S} [SystemState S] (state : S) (parent child : Block) : Prop :=
  parent.d ∈ child.parents ∧
  parent ∈ SystemState.blocks state ∧
  child  ∈ SystemState.blocks state

/--
Reflexive-transitive parent closure (paper §2.1, `causal(B)`).

`Reaches state B B'` means: starting from `B` and following parent pointers
zero or more times, we reach `B'`. This replaces the path-based definition
that lived in the original `Definitions.lean`.
-/
inductive Reaches {S : Type} [SystemState S] (state : S) : Block → Block → Prop where
  | refl : ∀ b, Reaches state b b
  | step : ∀ {b m parent},
      Reaches state b m →
      isParent state parent m →
      Reaches state b parent

/-- The causal history of `B`: the predicate `B' ↦ Reaches state B B'`. -/
abbrev causal {S} [SystemState S] (state : S) (B : Block) : Block → Prop :=
  Reaches state B

end BlockSynchroniser
