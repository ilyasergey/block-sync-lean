/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.
-/
import BlockSynchroniser.Block
import BlockSynchroniser.System

namespace BlockSynchroniser
namespace Beluga

/--
Beluga's extended block (paper §4.1).

Augments the abstract `Block` with three additional fields used by the
push/pull/admission-control machinery:

* `weaklinks` — digests of blocks the creator has received and accepted but
  did *not* select as parents. Used by the ImPoA pull mechanism (paper §4.3)
  as evidence of block availability.
* `watermark` — `n`-element array; entry `i` is the highest round number of
  any block received from validator `v_i`. Used by the AC reputation update
  rule (paper Figure 8, line 24).
* `ancestors` — `n`-element array; entry `i` is the highest round number of
  any of `v_i`'s blocks reachable from this block via strong links. Used by
  the live-vs-bulk classification in the pull protocol (paper §4.3.2).

`BelugaBlock` extends `Block`; the underlying block's `parents` field carries
the *strong links*, by paper convention.
-/
structure BelugaBlock extends Block where
  weaklinks : List BlockDigest := []
  watermark : List Round       := []
  ancestors : List Round       := []
  deriving Repr, DecidableEq

namespace BelugaBlock

/-- Number of validators implied by the watermark/ancestors length. A
well-formed Beluga block in a system with `n` validators has both arrays
of length `n`. -/
def watermarkSize (B : BelugaBlock) : Nat := B.watermark.length

/-- True iff `B`'s `watermark` and `ancestors` arrays have length `system.n`. -/
def WellSized (system : BlockSynchroniserSystem) (B : BelugaBlock) : Prop :=
  B.watermark.length = system.n ∧ B.ancestors.length = system.n

end BelugaBlock

end Beluga
end BlockSynchroniser
