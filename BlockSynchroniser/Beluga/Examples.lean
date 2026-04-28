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

/-- 4-validator, 1-Byzantine-budget all-honest system. Lean accepts up to
`f = 1` Byzantine validator; here all four are flagged honest, so the
trace exhibits a uniformly cooperative schedule. -/
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

/-- 7-validator, 2-Byzantine-budget all-honest system, illustrating the
`n = 3f + 1` BFT scaling at a medium committee. -/
def system7 : BlockSynchroniserSystem where
  n          := 7
  f          := 2
  k          := 0
  GST        := 0
  Δ          := 1
  validators := [(0, true), (1, true), (2, true), (3, true),
                 (4, true), (5, true), (6, true)]
  honestMajority        := by decide
  validatorsNodup       := by decide
  validatorCountCorrect := by decide
  validIds              := by decide
  byzantineBound        := by decide

/-- 13-validator, 4-Byzantine-budget all-honest system. The schedule's
fan-out is more visible at this size: a longer warm-up before round 1
opens, more accepts per round, and a wider spread in
`acceptedButNotStored` mid-trace. -/
def system13 : BlockSynchroniserSystem where
  n          := 13
  f          := 4
  k          := 0
  GST        := 0
  Δ          := 1
  validators := [(0, true), (1, true), (2, true), (3, true), (4, true),
                 (5, true), (6, true), (7, true), (8, true), (9, true),
                 (10, true), (11, true), (12, true)]
  honestMajority        := by decide
  validatorsNodup       := by decide
  validatorCountCorrect := by decide
  validIds              := by decide
  byzantineBound        := by decide

/-- Run the executable Beluga `step` `n` times starting from any system's
initial state. -/
def runWith (system : BlockSynchroniserSystem) (n : Nat) : BelugaState :=
  Nat.rec (BelugaState.init system) (fun _ s => step system s) n

/-- Run the executable Beluga `step` `n` times on `system4`. -/
def run (n : Nat) : BelugaState := runWith system4 n

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

/-- Per-validator current-round snapshot of a state. -/
def currentRounds (s : BelugaState) : List (ValidatorId × Round) :=
  s.validators.map (fun (vid, bv) => (vid, bv.currentRound))

/-- Count of accepted-but-not-stored digests for each validator. -/
def acceptedButNotStored (s : BelugaState) : List (ValidatorId × Nat) :=
  s.validators.map (fun (vid, bv) =>
    (vid, (bv.acceptedBlocks.filter
            (fun d => !bv.storedBlocks.contains d)).length))

/-- Operation-count breakdown by kind: `(propose, accept, store)`. -/
def opCountsByKind (s : BelugaState) : Nat × Nat × Nat :=
  s.emittedOperations.foldl
    (fun (p, a, st) op =>
      match op with
      | .block_propose _ _ _ => (p + 1, a, st)
      | .block_accept _ _   => (p, a + 1, st)
      | .block_store _ _    => (p, a, st + 1))
    (0, 0, 0)

/-! ## `#eval` smoke tests

The `step` function uses round-robin scheduling — it scans validators in
id order and applies the first available action (priority: propose →
accept → store → advance). vid 0 exhausts its actions before vid 1 takes
over, then vid 2, then vid 3.

### Trace growth

Operation count grows monotonically with steps. -/
#eval (run 4).emittedOperations.length
#eval (run 12).emittedOperations.length
#eval (run 36).emittedOperations.length

/-! ### Operation breakdown

The triple `(proposes, accepts, stores)` shows how many of each kind of
operation have been emitted. Proposes are bounded by validators × rounds
proposed for; accepts and stores fan out as the schedule progresses. -/
#eval opCountsByKind (run 36)

/-! ### Round-0 proposer set

Distinct round-0 proposers grow as the round-robin scheduler reaches new
validators. -/
#eval proposersFor (run 4) 0
#eval proposersFor (run 12) 0
#eval proposersFor (run 40) 0

/-! ### Per-validator current round

Initially everyone is at round 0. As proposing/accepting/storing fan out
and quorum is reached, validators advance. -/
#eval currentRounds (run 0)    -- all at round 0
#eval currentRounds (run 60)   -- some validators have advanced

/-! ### Accepted-but-unstored backlog

The store action follows accept; in flight, the per-validator backlog can
be non-zero. After the schedule has caught up it returns to zero. -/
#eval acceptedButNotStored (run 20)

/-! ### Block pool size -/
#eval (run 20).blocks.length
#eval (run 60).blocks.length

/-! ### Medium committee

A 7-validator system with `n = 3f + 1`, `f = 2`. The trace fans out across
seven honest proposers. -/
#eval (runWith system7 80).emittedOperations.length
#eval proposersFor (runWith system7 80) 0

/-! ### Large committee

A 13-validator system with `f = 4`. -/
#eval (runWith system13 200).emittedOperations.length
#eval proposersFor (runWith system13 200) 0

/-! ### Pretty-printed log -/
#eval IO.println (reprLog (run 20))

end Examples
end Beluga
end BlockSynchroniser
