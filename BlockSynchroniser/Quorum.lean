/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.
-/
import BlockSynchroniser.System

namespace BlockSynchroniser
namespace Quorum

/-- A quorum is a duplicate-free list of `≥ 2f+1` registered validator ids. -/
def IsQuorum (system : BlockSynchroniserSystem) (Q : List ValidatorId) : Prop :=
  Q.Nodup ∧
  Q.length ≥ 2 * system.f + 1 ∧
  ∀ vid ∈ Q, ∃ pair ∈ system.validators, pair.1 = vid

/--
**Quorum intersection.**

Any two quorums in a system with `n ≥ 3f+1` validators share at least `f+1`
validators. Since the system tolerates at most `f` Byzantine validators, this
guarantees at least one *honest* validator in the intersection — the workhorse
lemma for every BFT safety argument.

**Proof idea (cardinality / pigeonhole).**
By definition, `|Q₁| ≥ 2f+1` and `|Q₂| ≥ 2f+1`. Both lie in the universe of
`n ≤ 3f+1` registered validators (after dedup). Inclusion–exclusion:
`|Q₁ ∩ Q₂| = |Q₁| + |Q₂| - |Q₁ ∪ Q₂| ≥ (2f+1) + (2f+1) - n ≥ f+1`.
-/
theorem quorumIntersection
    (system : BlockSynchroniserSystem)
    (Q₁ Q₂ : List ValidatorId)
    (h₁ : IsQuorum system Q₁)
    (h₂ : IsQuorum system Q₂) :
    ∃ shared : List ValidatorId,
      shared.Nodup ∧
      shared.length ≥ system.f + 1 ∧
      ∀ vid ∈ shared, vid ∈ Q₁ ∧ vid ∈ Q₂ := by
  sorry

end Quorum
end BlockSynchroniser
