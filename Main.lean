import BlockSynchroniser
import BlockSynchroniser.Beluga.Examples

open BlockSynchroniser Beluga Examples

def main : IO Unit := do
  IO.println "=== Beluga honest-synchronous trace ==="
  IO.println s!"system: n=4, f=1, k=0, all 4 validators honest"
  IO.println ""
  let nSteps := 20
  let s := run nSteps
  IO.println s!"After {nSteps} executable `step` calls:"
  IO.println s!"  total ops emitted: {s.emittedOperations.length}"
  IO.println s!"  blocks in pool:    {s.blocks.length}"
  IO.println s!"  round-0 distinct proposers: {proposersFor s 0}"
  IO.println ""
  IO.println "Operation log:"
  IO.println (reprLog s)
