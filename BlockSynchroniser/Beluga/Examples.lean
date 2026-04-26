/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Executable examples driving the Beluga protocol on concrete systems.
Used by `Main.lean` and for `#eval` smoke tests.
-/
import BlockSynchroniser.Beluga.Protocol

namespace BlockSynchroniser
namespace Beluga
namespace Examples

/-- 4-validator, 1-Byzantine-budget honest system used by the executable
demos. All four validators are honest; `k = 0` so blocks need no parents. -/
def system4 : BlockSynchroniserSystem where
  n          := 4
  f          := 1
  k          := 0
  GST        := 0
  Δ          := 1
  validators := [(0, true), (1, true), (2, true), (3, true)]
  honestMajority        := by decide
  validatorsNodup       := by decide
  validatorCountCorrect := by decide
  validIds              := by decide
  byzantineBound        := by decide

/-- Run the executable Beluga `step` `n` times starting from the initial
state of `system4`. -/
def run (n : Nat) : BelugaState :=
  Nat.rec (BelugaState.init system4) (fun _ s => step system4 s) n

/-- Pretty-print one operation. -/
def reprOp : ValidatorOperation → String
  | .block_propose vid B r =>
      s!"propose vid={vid} round={r} digest={B.d} parents={B.parents}"
  | .block_accept  vid d   => s!"accept  vid={vid} digest={d}"
  | .block_store   vid B   => s!"store   vid={vid} digest={B.d}"

/-- Pretty-print the operation log of a state (one op per line). -/
def reprLog (s : BelugaState) : String :=
  String.intercalate "\n"
    (s.emittedOperations.zipIdx.map (fun (op, i) => s!"  {i}: {reprOp op}"))

/-- Distinct round-`r` proposers in the operation log. -/
def proposersFor (s : BelugaState) (r : Round) : List ValidatorId :=
  (s.emittedOperations.filterMap (fun op =>
    match op with
    | .block_propose vid _ r' => if r' = r then some vid else none
    | _ => none)).eraseDups

/-! ## `#eval` smoke tests

The `step` function uses round-robin scheduling — it scans validators in id
order and applies the first available action (propose → accept → store →
advance). So vid 0 fully exhausts its actions before vid 1 takes over,
making the early trace look concentrated. Total ops grows monotonically,
which is what these `#eval`s exercise. -/

-- Operation count after 4 steps.
#eval (run 4).emittedOperations.length

-- Distinct round-0 proposers after 4 steps. Grows as the round-robin
-- scheduler reaches new validators.
#eval proposersFor (run 4) 0

-- After 20 steps, the trace has progressed substantially.
#eval (run 20).emittedOperations.length

-- Pretty-printed first 20 ops.
#eval IO.println (reprLog (run 20))

end Examples
end Beluga
end BlockSynchroniser
