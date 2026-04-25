/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Admission well-formedness as a trace invariant of `belugaTrace`.

This module surfaces the DAG-protocol structural property that the
Beluga paper takes as obvious: every block at a positive round
references at least `2f+1` distinct-author parents from the
immediately preceding round.

It is *not* a hypothesis on the adversary — it follows from the
executable `step`'s scheduling discipline. `tryActFor` only fires
`doAdvance` once `allProposedFor` is true (every validator has
proposed for the current round), so when a validator advances to
round `r` and subsequently calls `doPropose`, the state already
contains every round-`(r-1)` proposal. Those round-`(r-1)` blocks
are the parent set of the new round-`r` block, and there are
`n ≥ 2f+1` of them by distinct authors.

`belugaTrace_admissionWellFormed` is the trace-level statement;
[`Mysticeti.Safety.lemma13_cert_persistence`](Mysticeti/Safety.lean)
is its main consumer (replaces the previous two ad-hoc hypotheses
`h_cert_base` and `h_dag_parent`).
-/
import BlockSynchroniser.Block
import BlockSynchroniser.System
import BlockSynchroniser.State
import BlockSynchroniser.Beluga.Protocol

namespace BlockSynchroniser
namespace Beluga

/-- A state's blocks satisfy *admission well-formedness* if every block
at round `> 0` has at least `2f+1` distinct-author parents from the
immediately preceding round, all themselves in the state.

This is the structural DAG invariant the paper treats as obvious in
the proofs of Mysticeti-Beluga safety (Appendix D.3). It is a
consequence of the protocol's parent-selection rule + Beluga's
admission control — **not** an adversary constraint.
-/
def AdmissionWellFormed (system : BlockSynchroniserSystem) {S} [SystemState S]
    (state : S) : Prop :=
  ∀ B ∈ SystemState.blocks state, B.r > 0 →
    ∃ parents : List Block,
      parents.length ≥ 2 * system.f + 1 ∧
      (parents.map (·.author)).Nodup ∧
      ∀ P ∈ parents,
        P ∈ SystemState.blocks state ∧
        P.d ∈ B.parents ∧
        P.r + 1 = B.r

/-- The Beluga trace preserves admission well-formedness.

Proof sketch: induct on the trace step `k`. At step 0, `BelugaState.init`
has empty `blocks`; vacuously true. At step `k+1`, the only way new
blocks enter `s.blocks` is through the executable `step`'s `doPropose`
branch. By the gating logic in `tryActFor` (`!hasProposedFor` for the
proposing validator at round `r`, plus `allProposedFor` is required
*before* `doAdvance`), any validator that has reached `currentRound = r`
with `r > 0` has done so through a chain of advances, each gated by
`allProposedFor` of the preceding round. Hence at the moment the new
round-`r` block is created, `s.blocks` already contains every
validator's round-`(r-1)` proposal — `n` blocks from `n` distinct
authors, satisfying `length ≥ 2f+1` and Nodup-by-author. The new
block's `parents` are exactly the digests of those round-`(r-1)`
blocks (per `doPropose`'s parent construction).

Currently a stub — proof requires reasoning about the cumulative
state of the trace, queued for a dedicated trace-invariant round.
-/
theorem belugaTrace_admissionWellFormed
    (system : BlockSynchroniserSystem) (k : Nat) :
    AdmissionWellFormed system (belugaTrace system k) := by
  sorry

end Beluga
end BlockSynchroniser
