/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.
-/
import BlockSynchroniser.Block

namespace BlockSynchroniser

/--
The three primitives of the block synchronizer interface (paper §2.1):

* `block_propose_i(B, r)` — `v_i` proposes `B` for round `r`.
* `block_accept_i(B.d)`   — `v_i` deems `B` acceptable.
* `block_store_i(B)`      — `v_i` has stored `B` locally.
-/
inductive ValidatorOperation where
  | block_propose (author : ValidatorId) (block : Block) (round : Round) : ValidatorOperation
  | block_accept  (id : ValidatorId) (d : BlockDigest)                   : ValidatorOperation
  | block_store   (id : ValidatorId) (block : Block)                     : ValidatorOperation
  deriving Repr

end BlockSynchroniser
