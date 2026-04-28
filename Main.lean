import BlockSynchroniser
import BlockSynchroniser.Beluga.Examples

open BlockSynchroniser Beluga Examples

/-- Pretty-print a final-state summary for any system. -/
def printSummary (label : String) (s : BelugaState) : IO Unit := do
  let (p, a, st) := opCountsByKind s
  IO.println s!"=== {label} ==="
  IO.println s!"  total ops emitted: {s.emittedOperations.length}"
  IO.println s!"    proposes: {p}"
  IO.println s!"    accepts:  {a}"
  IO.println s!"    stores:   {st}"
  IO.println s!"  blocks in pool:    {s.blocks.length}"
  IO.println s!"  round-0 proposers: {proposersFor s 0}"
  IO.println s!"  round-1 proposers: {proposersFor s 1}"
  IO.println s!"  current rounds:    {currentRounds s}"

/-- Print the help text. -/
def printHelp : IO Unit := do
  IO.println "Usage: blocksynchroniser <command> [steps]"
  IO.println ""
  IO.println "Commands:"
  IO.println "  small [n]    Run the 4-validator (f=1) all-honest system for n steps (default 20)."
  IO.println "  medium [n]   Run the 7-validator (f=2) all-honest system."
  IO.println "  large [n]    Run the 13-validator (f=4) all-honest system."
  IO.println "  log [n]      Print the operation log of the small system."
  IO.println "  compare [n]  Run small, medium, and large; print summaries side by side."
  IO.println "  help         Show this help text."
  IO.println ""
  IO.println "If no command is given, runs `small 20` and prints the operation log."

/-- Parse an optional step count argument (default 20). -/
def parseSteps : List String → Nat
  | []       => 20
  | s :: _   => s.toNat?.getD 20

def main (args : List String) : IO Unit := do
  match args with
  | [] =>
    let s := run 20
    printSummary "Small system (n=4, f=1, all honest, 20 steps)" s
    IO.println ""
    IO.println "Operation log:"
    IO.println (reprLog s)
  | "help" :: _ | "--help" :: _ | "-h" :: _ =>
    printHelp
  | "small" :: rest =>
    let n := parseSteps rest
    printSummary s!"Small system (n=4, f=1, all honest, {n} steps)" (runWith system4 n)
  | "medium" :: rest =>
    let n := parseSteps rest
    printSummary s!"Medium system (n=7, f=2, all honest, {n} steps)" (runWith system7 n)
  | "large" :: rest =>
    let n := parseSteps rest
    printSummary s!"Large system (n=13, f=4, all honest, {n} steps)" (runWith system13 n)
  | "log" :: rest =>
    let n := parseSteps rest
    let s := runWith system4 n
    printSummary s!"Small system (n=4, f=1, all honest, {n} steps)" s
    IO.println ""
    IO.println "Operation log:"
    IO.println (reprLog s)
  | "compare" :: rest =>
    let n := parseSteps rest
    printSummary s!"Small (n=4) — {n} steps" (runWith system4 n)
    IO.println ""
    printSummary s!"Medium (n=7) — {n} steps" (runWith system7 n)
    IO.println ""
    printSummary s!"Large (n=13) — {n} steps" (runWith system13 n)
  | cmd :: _ =>
    IO.println s!"Unknown command: {cmd}"
    IO.println ""
    printHelp
