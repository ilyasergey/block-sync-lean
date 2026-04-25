/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.
-/
import BlockSynchroniser.State

namespace BlockSynchroniser

/-- A trace is an infinite sequence of system states indexed by step number. -/
def Trace (S : Type) [SystemState S] := Nat → S

/-- Trace induction principle: a property holding at step 0 and preserved by
single-step transitions holds at every step. -/
theorem traceInduction {S : Type} [SystemState S]
    (P : S → Prop)
    (trace : Trace S)
    (zero : P (trace 0))
    (step : ∀ i, P (trace i) → P (trace (i + 1))) :
    ∀ i, P (trace i) :=
  fun i => Nat.rec zero (fun i ih => step i ih) i

/-- "Eventually" combinator over a trace: there exists a step `k' ≥ k` at which
`P k' (trace k')` holds. -/
def Eventually {S} [SystemState S] (trace : Trace S) (k : Nat)
    (P : Nat → S → Prop) : Prop :=
  ∃ k' ≥ k, P k' (trace k')

/-- The operation log of the state at step `k` of `trace`. -/
abbrev opsAt {S} [SystemState S] (trace : Trace S) (k : Nat) : List ValidatorOperation :=
  SystemState.emittedOperations (trace k)

/-- True iff `op` is in the operation log of `state`. -/
def Emitted {S} [SystemState S] (state : S) (op : ValidatorOperation) : Prop :=
  op ∈ SystemState.emittedOperations state

/-- True iff validator `vid` has accepted block digest `d` in `state`. -/
def HasAccepted {S} [SystemState S] (state : S) (vid : ValidatorId) (d : BlockDigest) : Prop :=
  Emitted state (.block_accept vid d)

/-- True iff validator `vid` has stored block `B` in `state`. -/
def HasStored {S} [SystemState S] (state : S) (vid : ValidatorId) (B : Block) : Prop :=
  Emitted state (.block_store vid B)

/-- True iff validator `vid` has proposed block `B` for round `r` in `state`. -/
def HasProposed {S} [SystemState S] (state : S) (vid : ValidatorId) (B : Block) (r : Round) : Prop :=
  Emitted state (.block_propose vid B r)

/-- Author of the round-`round` block whose digest is `d`, if such a propose
operation appears in `ops`. -/
def authorOfDigest (ops : List ValidatorOperation) (round : Round) (d : BlockDigest) :
    Option ValidatorId :=
  (ops.find? (fun op =>
    match op with
    | .block_propose _ block r => block.d == d && r == round
    | _ => false)).bind (fun op =>
      match op with
      | .block_propose author _ _ => some author
      | _ => none)

end BlockSynchroniser
