import BlockSynchroniser
import BlockSynchroniser.Definitions

open BlockSynchroniser.Examples

def main : IO Unit :=
  IO.println s!"Hello, BlockSynchroniser! System has {exampleSystem.n} validators."
