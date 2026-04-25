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
Honest validators don't reference equivocating parents — *cross-block*
version.

Captures the safety property that, in any state induced by a correct
execution, no two honest validators (whether the same one or two distinct
ones) ever reference conflicting blocks for the same `(author, round)`
pair. In Beluga this is enforced by the AC module (Phase 4); we state
it abstractly here as a hypothesis on the state.

The within-block specialization (`B₁ = B₂`) is the simpler form
"honest validators don't include two parents from the same proposer
round in their own block." The cross-block form additionally rules out
"honest validators reference different round-`r` blocks of the same
author across two of their own blocks" — needed for `certified_unique`'s
proof where the shared honest validator may have referenced `B₁` and
`B₂` from two different blocks of theirs.
-/
def NoEquivocationInParents (system : BlockSynchroniserSystem) {S} [SystemState S]
    (state : S) : Prop :=
  ∀ B₁ B₂ parent₁ parent₂,
    B₁ ∈ SystemState.blocks state →
    B₂ ∈ SystemState.blocks state →
    isHonestValidator system B₁.author = true →
    isHonestValidator system B₂.author = true →
    parent₁ ∈ SystemState.blocks state →
    parent₂ ∈ SystemState.blocks state →
    parent₁.d ∈ B₁.parents →
    parent₂.d ∈ B₂.parents →
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
By `certificatePattern`, `|S₁| > 2f` and `|S₂| > 2f`, so both qualify as
quorums. By `Quorum.quorumIntersection`, they share at least `f+1`
validators; since at most `f` are Byzantine, at least one *honest*
validator `h ∈ S₁ ∩ S₂`.

`h ∈ S₁` means there exists a block `C₁` in `state.blocks` with
`C₁.author = h` and `B₁.d ∈ C₁.parents`. Similarly `h ∈ S₂` gives a
block `C₂` with `C₂.author = h` and `B₂.d ∈ C₂.parents`. Note `C₁` and
`C₂` may or may not be the same block.

Since `h` is honest, both `C₁` and `C₂` are honestly-authored. Apply
`NoEquivocationInParents` (cross-block form) to `(C₁, C₂, B₁, B₂)`,
using `h_same_author` and `h_same_round` to discharge the equality
hypotheses. Conclude `B₁ = B₂`.

This proof depends on `Quorum.quorumIntersection` (currently pending).
Queued for Aristotle round 2 — see [docs/aristotle-projects.md](../../docs/aristotle-projects.md).
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
