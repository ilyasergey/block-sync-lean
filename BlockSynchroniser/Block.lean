/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.
-/

namespace BlockSynchroniser

abbrev ValidatorId := Nat
abbrev Round := Nat
abbrev BlockDigest := Nat
abbrev Transaction := String

/--
A block (paper §2.1).

Carries a round number, the digest, the creator's identifier, the digests of its
parent blocks, and a payload of transactions. The paper additionally specifies
the creator's signature on `B`; we omit it here since it plays no role in the
abstract synchronizer's properties (Definition 1).
-/
structure Block where
  r       : Round
  author  : ValidatorId
  d       : BlockDigest
  parents : List BlockDigest
  payload : List Transaction
  deriving Repr, DecidableEq

end BlockSynchroniser
