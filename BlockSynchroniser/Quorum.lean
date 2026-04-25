/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.
-/
import Mathlib.Tactic
import BlockSynchroniser.System

set_option linter.unusedSimpArgs false
set_option linter.style.refine false

namespace BlockSynchroniser
namespace Quorum

/--
A quorum is a duplicate-free list of `≥ 2f+1` registered validator ids.

*Not paper-specific.* Standard BFT quorum: any quorum-sized set of voters is
guaranteed to overlap any other quorum in at least `f+1` participants, of
whom at least one is honest (since at most `f` are Byzantine). The paper
uses this implicitly throughout §5 and Appendix D.
-/
def IsQuorum (system : BlockSynchroniserSystem) (Q : List ValidatorId) : Prop :=
  Q.Nodup ∧
  Q.length ≥ 2 * system.f + 1 ∧
  ∀ vid ∈ Q, ∃ pair ∈ system.validators, pair.1 = vid

/-
**Quorum intersection.** *Not in the paper as a numbered lemma — it is the
standard BFT lemma the paper relies on throughout §5 and Appendix D.*

Any two quorums in a system with `n = 3f+1` validators share at least `f+1`
validators. Since the system tolerates at most `f` Byzantine validators, this
guarantees at least one *honest* validator in the intersection — the workhorse
lemma for every BFT safety argument.

The hypothesis `system.n = 3 * system.f + 1` is essential: with `n > 3f+1` the
classical 2f+1-quorum bound `(2f+1) + (2f+1) - n` drops below `f+1`. Real
deployments with larger `n` would adjust quorum size to `⌈(n+f+1)/2⌉`; we
follow the paper's standard convention.

**Proof idea (cardinality / inclusion-exclusion).**
By `IsQuorum`, `|Q₁| ≥ 2f+1` and `|Q₂| ≥ 2f+1`. Both lie in the validator
universe `U` (after dedup), with `|U| = n = 3f+1` from the hypothesis +
`validatorIdsUnique` + `validatorCountCorrect`. Inclusion-exclusion:

  `|Q₁ ∩ Q₂| = |Q₁| + |Q₂| - |Q₁ ∪ Q₂| ≥ (2f+1) + (2f+1) - n = f+1`.

The Lean form: convert `Q₁`, `Q₂` to `Finset` (preserves cardinality via
`Nodup`); apply `Finset.card_inter_add_card_union`; use `Finset.card_le_card`
for `Q₁.toFinset ∪ Q₂.toFinset ⊆ U`; bound and conclude. Queued for
Aristotle round 2 — see [docs/aristotle-projects.md](../docs/aristotle-projects.md).
-/
theorem quorumIntersection
    (system : BlockSynchroniserSystem)
    (Q₁ Q₂ : List ValidatorId)
    (h₁ : IsQuorum system Q₁)
    (h₂ : IsQuorum system Q₂)
    (hN : system.n = 3 * system.f + 1) :
    ∃ shared : List ValidatorId,
      shared.Nodup ∧
      shared.length ≥ system.f + 1 ∧
      ∀ vid ∈ shared, vid ∈ Q₁ ∧ vid ∈ Q₂ := by
  unfold IsQuorum at *;
  refine' ⟨ Q₁.toFinset ∩ Q₂.toFinset |> Finset.toList, _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
  · exact Finset.nodup_toList _;
  · have h_union : (Q₁.toFinset ∪ Q₂.toFinset).card ≤ system.n := by
      refine' le_trans ( Finset.card_le_card _ ) _;
      exact ( system.validators.map ( ·.1 ) ).toFinset;
      · intro x hx; aesop;
      · exact le_trans ( Multiset.toFinset_card_le _ ) ( by simp [ system.validatorCountCorrect ] );
    have := Finset.card_union_add_card_inter Q₁.toFinset Q₂.toFinset; simp_all +decide [ List.toFinset_card_of_nodup ] ; linarith;

end Quorum
end BlockSynchroniser