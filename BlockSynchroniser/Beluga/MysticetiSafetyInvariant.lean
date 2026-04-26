/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Trace invariants packaged for Mysticeti-Beluga safety (Appendix D.3).

`Mysticeti/Safety.lean` states the paper's L13/L15 against an abstract
`SystemState`; each of those lemmas takes four protocol-invariant
hypotheses (`AdmissionWellFormed`, `NoEquivocationInParents`, the
honest-author uniqueness assumption, and the authors-are-registered
side condition). For the executable `belugaTrace` instantiation, these
are not assumptions: three follow structurally from invariants already
established in `Beluga/AdmissionInvariant.lean` and `Beluga/Protocol.lean`,
and the fourth (`authorsValid`) is a one-line trace invariant about
emitted operations.

This module bundles the four facts as `MysticetiSafetyInv` and proves
the bundle for `belugaTrace`. `Mysticeti/Safety.lean` then provides
belugaTrace-specialised wrappers `lemma13_cert_persistence_belugaTrace`
and `lemma15_unique_cert_belugaTrace` whose only remaining hypotheses
are the genuine BFT side conditions (`hN`, `h_byz_bound`, `hids`) —
paper assumptions that cannot be derived from the executable trace.
-/
import BlockSynchroniser.Beluga.Patterns
import BlockSynchroniser.Beluga.AdmissionInvariant
import BlockSynchroniser.Beluga.Protocol

namespace BlockSynchroniser
namespace Beluga

/-- Trace invariants needed by Mysticeti-Beluga safety (Appendix D.3).

Bundles four facts that L13/L15 take as explicit hypotheses but that
hold of `belugaTrace` for free:

| field | corresponds to L13/L15 hypothesis |
|---|---|
| `admission` | `h_admission : AdmissionWellFormed system state` |
| `uniqueByAuthorRound` | `h_honest_unique` (in fact stronger — drops the honesty hypothesis) |
| `noEquivocation` | `h_no_eq : NoEquivocationInParents system state` |
| `authorsValid` | `h_authors_valid` |
-/
structure MysticetiSafetyInv (system : BlockSynchroniserSystem) (s : BelugaState) :
    Prop where
  /-- DAG admission well-formedness — closed in
  [`AdmissionInvariant.lean`](AdmissionInvariant.lean) by
  `belugaTrace_admissionWellFormed`. -/
  admission : AdmissionWellFormed system s
  /-- Author + round determine the block (paper §4.4). Stronger than
  L13's `h_honest_unique`: no honesty hypothesis is needed because
  `BlockInv.uniquePropose` is total. -/
  uniqueByAuthorRound :
    ∀ B₁ ∈ s.blocks, ∀ B₂ ∈ s.blocks,
      B₁.author = B₂.author → B₁.r = B₂.r → B₁ = B₂
  /-- Cross-block parent agreement (paper Appendix D.3 implicit fact). -/
  noEquivocation : NoEquivocationInParents system s
  /-- Every block author is a registered validator. -/
  authorsValid : ∀ B ∈ s.blocks, ∃ p ∈ system.validators, p.1 = B.author

/-- Structural derivation of the `uniqueByAuthorRound` conjunct from
`BlockInv`. No honesty hypothesis is required: `BlockInv.uniquePropose`
gives uniqueness of every `(author, round)` pair, honest or not. -/
private lemma uniqueByAuthorRound_of_blockInv
    {system : BlockSynchroniserSystem} {s : BelugaState}
    (h_inv : BlockInv system s) :
    ∀ B₁ ∈ s.blocks, ∀ B₂ ∈ s.blocks,
      B₁.author = B₂.author → B₁.r = B₂.r → B₁ = B₂ := by
  intro B₁ hB₁ B₂ hB₂ ha hr
  have hp₁ := h_inv.hasPropose B₁ hB₁
  have hp₂ := h_inv.hasPropose B₂ hB₂
  rw [ha, hr] at hp₁
  exact h_inv.uniquePropose _ _ _ _ hp₁ hp₂

/-- Structural derivation of `NoEquivocationInParents` from `BlockInv`.
The two parents-with-same-(author, round) are themselves blocks in
state, so `uniqueByAuthorRound_of_blockInv` applies directly. -/
private lemma noEquivocation_of_blockInv
    {system : BlockSynchroniserSystem} {s : BelugaState}
    (h_inv : BlockInv system s) :
    NoEquivocationInParents system s := by
  intro B₁ B₂ p₁ p₂ _ _ _ _ hp₁_in hp₂_in _ _ ha hr
  exact uniqueByAuthorRound_of_blockInv h_inv p₁ hp₁_in p₂ hp₂_in ha hr

/-- The Beluga trace satisfies the Mysticeti safety invariant bundle.

Three of four conjuncts are discharged from existing trace invariants:
- `admission` ← `belugaTrace_admissionWellFormed`,
- `uniqueByAuthorRound` ← `blockInv_trace` + `BlockInv.uniquePropose`,
- `noEquivocation` ← `blockInv_trace` + `BlockInv.uniquePropose`.

The `authorsValid` conjunct is currently a stub queued for
delegation: it requires a separate trace invariant about emitted
operations (every `block_propose vid B r` op has `vid` registered in
`system.validators`). -/
theorem belugaTrace_satisfies_mysticetiSafetyInv
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (k : Nat) :
    MysticetiSafetyInv system (belugaTrace system k) := by
  have h_blockInv := blockInv_trace system hids k
  refine
    { admission := belugaTrace_admissionWellFormed system k
      uniqueByAuthorRound := uniqueByAuthorRound_of_blockInv h_blockInv
      noEquivocation := noEquivocation_of_blockInv h_blockInv
      authorsValid := ?_ }
  sorry

end Beluga
end BlockSynchroniser
