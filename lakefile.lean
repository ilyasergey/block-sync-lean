import Lake
open Lake DSL

package «BlockSynchroniser» where
  -- add package configuration options here

require batteries from
    git "https://github.com/leanprover-community/batteries" @ "v4.28.0"
require mathlib from
    git "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

-- require ssreflect from
--     git "https://github.com/verse-lab/lean-ssr.git" @ "master"


lean_lib «BlockSynchroniser» where
  -- add library configuration options here

@[default_target]
lean_exe «blocksynchroniser» where
  root := `Main
