/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Block patterns (paper §4.4).
-/
import BlockSynchroniser.Block
import BlockSynchroniser.System
import BlockSynchroniser.State
import BlockSynchroniser.Quorum

namespace BlockSynchroniser
namespace Beluga

/-- The distinct authors of blocks in `state` that reference `B` *as a parent*
(strong link). Used by both pattern definitions below. -/
def strongReferencerAuthors {S} [SystemState S] (state : S) (B : Block) : List ValidatorId :=
  ((SystemState.blocks state).filter (fun B' => B.d ∈ B'.parents)).map (·.author)
    |>.eraseDups

/--
**Availability pattern (paper §4.4).**

`B` forms an availability pattern if it is referenced by more than `f` distinct
validators' blocks. Per the paper, "referenced" includes both strong links
(parents) and weak links (weaklinks). For now we conservatively count strong
links only — every weak-link-included reference is at least as inclusive, so
this lower-bounds the paper's notion. The fully-faithful version that includes
weaklinks will land alongside Beluga-specific state in Phase 4.

A block forming an availability pattern is called *available*: at least one
honest validator can attest to its causal availability.
-/
def availabilityPattern (system : BlockSynchroniserSystem) {S} [SystemState S]
    (state : S) (B : Block) : Prop :=
  (strongReferencerAuthors state B).length > system.f

/--
**Certificate pattern (paper §4.4).**

`B` forms a certificate pattern if it is referenced *as parents* by more than
`2f` distinct validators' blocks. A block forming a certificate pattern is
called *certified*; certificates underlie consensus uniqueness.
-/
def certificatePattern (system : BlockSynchroniserSystem) {S} [SystemState S]
    (state : S) (B : Block) : Prop :=
  (strongReferencerAuthors state B).length > 2 * system.f

/-- An *available* block (paper §4.4 — block forming an availability pattern). -/
abbrev available := availabilityPattern

/-- A *certified* block (paper §4.4 — block forming a certificate pattern). -/
abbrev certified := certificatePattern

/--
Honest validators don't reference equivocating parents.

Captures the safety property that, in any state induced by a correct execution,
honest validators never include two parents from the same `(author, round)`
pair. In Beluga this is enforced by the AC module (Phase 4); we state it
abstractly here as a hypothesis on the state.
-/
def NoEquivocationInParents (system : BlockSynchroniserSystem) {S} [SystemState S]
    (state : S) : Prop :=
  ∀ B parent₁ parent₂,
    B ∈ SystemState.blocks state →
    isHonestValidator system B.author →
    parent₁ ∈ SystemState.blocks state →
    parent₂ ∈ SystemState.blocks state →
    parent₁.d ∈ B.parents →
    parent₂.d ∈ B.parents →
    parent₁.author = parent₂.author →
    parent₁.r = parent₂.r →
    parent₁ = parent₂

/--
**Uniqueness of certified blocks per `(author, round)` (paper §4.4).**

> *"the certificate pattern implies uniqueness: for any validator and round,
> at most one block can become certified"* — paper §4.4 (page 9).

Stated as an informal consequence in §4.4 (no lemma number); we formalize it
here. Specializing `B₁.author = B₂.author = leader(r)` gives Appendix D
**Lemma 15** ("at most one leader block can be certified for any round r"),
which is the load-bearing form for the Mysticeti-Beluga safety theorem
(Phase 6).

PROVIDED SOLUTION
Let `S₁ = strongReferencerAuthors state B₁` and `S₂ = strongReferencerAuthors state B₂`.
By `certificatePattern`, `|S₁| > 2f` and `|S₂| > 2f`. Both lists are sublists
of `system.validators`, so by `Quorum.quorumIntersection` they share at least
`f + 1` elements; in particular at least one *honest* validator `h ∈ S₁ ∩ S₂`
(since at most `f` Byzantines exist). The block `B_h` authored by `h` lists
both `B₁.d` and `B₂.d` among its parents. By `NoEquivocationInParents` applied
to `B_h`, `B₁` and `B₂` (which share author and round), `B₁ = B₂`.
-/
theorem certified_unique
    {S} [SystemState S] (system : BlockSynchroniserSystem) (state : S)
    (h_no_equivocation : NoEquivocationInParents system state)
    (B₁ B₂ : Block)
    (h_cert₁ : certified system state B₁)
    (h_cert₂ : certified system state B₂)
    (h_same_author : B₁.author = B₂.author)
    (h_same_round  : B₁.r      = B₂.r) :
    B₁ = B₂ := by
  sorry

end Beluga
end BlockSynchroniser
