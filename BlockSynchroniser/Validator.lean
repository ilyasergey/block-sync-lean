/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.
-/
import BlockSynchroniser.Block

namespace BlockSynchroniser

/-- Local view of a single validator: which block digests it has accepted, which it has stored. -/
structure Validator where
  acceptedBlocks : List BlockDigest
  storedBlocks   : List BlockDigest
  deriving Repr, DecidableEq

end BlockSynchroniser
