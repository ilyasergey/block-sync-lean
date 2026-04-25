/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Admission Control (paper §4.2; pseudocode in Figure 8, Appendix E,
lines 14–22 and 1–13).
-/
import BlockSynchroniser.Block
import BlockSynchroniser.System
import BlockSynchroniser.State
import BlockSynchroniser.Trace
import BlockSynchroniser.Beluga.State
import BlockSynchroniser.Beluga.Reputation

namespace BlockSynchroniser
namespace Beluga

/--
"Acceptable" predicate (paper §4.2): a block `B` is acceptable for `vid` in
`state` if `vid` has output `block_accept_i(B.d)`. The paper's broader
notion ("or can otherwise ensure ancestors are available") via ImPoA lands
alongside the pull formalization.
-/
def isAcceptable {S} [SystemState S]
    (state : S) (vid : ValidatorId) (B : Block) : Prop :=
  HasAccepted state vid B.d

/-- Bool-valued version of `isAcceptable` (decidable membership in the
operation log). -/
def isAcceptableB {S} [SystemState S]
    (state : S) (vid : ValidatorId) (B : Block) : Bool :=
  decide (HasAccepted state vid B.d)

/-- The set of round-`(r-1)` blocks `vid` has received that are acceptable
(parent candidates for a new round-`r` block). -/
def filterAcceptable {S} [SystemState S]
    (state : S) (vid : ValidatorId) (candidates : List Block) (r : Round) :
    List Block :=
  candidates.filter (fun B => B.r == r - 1 && isAcceptableB state vid B)

/--
Top `2f+1` blocks in `blocks` ranked by their authors' reputations
(descending). Used by `acParentSelection` to pick high-reputation parents.
-/
def topByReputation
    (system : BlockSynchroniserSystem)
    (rt : ReputationTable) (blocks : List Block) : List Block :=
  let scored  := blocks.map (fun B => (B, rt.lookup B.author))
  let sorted  := scored.toArray.qsort (fun a b => decide (a.2 > b.2)) |>.toList
  (sorted.take (2 * system.f + 1)).map (·.1)

/--
**`AC_parent_selection(r, B)`** (paper Figure 8, lines 14–17).

Filter the candidate set `B` (the latest blocks `vid` has received from each
peer with round `≤ r-1`) to those that are round-`(r-1)` acceptable, then
take the top `2f+1` by creator reputation.
-/
def acParentSelection {S} [SystemState S]
    (system : BlockSynchroniserSystem)
    (state : S) (rt : ReputationTable) (vid : ValidatorId)
    (candidates : List Block) (r : Round) : List Block :=
  topByReputation system rt (filterAcceptable state vid candidates r)

/--
**Round-advancement rule (i)** (paper §4.2).

`vid` is allowed to advance to round `r+1` (creating a round-`(r+1)` block)
when it has accepted `≥ 2f+1` round-`r` blocks whose authors' reputations
exceed the threshold `R_t = R_{2f+1} - R_L`.

The dual rule (ii) — per-round timeout `T_rd` expires — is a wall-clock
condition handled in the protocol semantics layer (Phase 4d/e).
-/
def canAdvanceByQuorum {S} [SystemState S]
    (system : BlockSynchroniserSystem)
    (state : S) (rt : ReputationTable) (vid : ValidatorId)
    (R_L : Nat) (r : Round) : Prop :=
  let received := SystemState.blocks state
  let acceptable := filterAcceptable state vid received r
  let highRep := acceptable.filter (fun B =>
    decide (rt.lookup B.author > reputationThreshold system rt R_L))
  highRep.length ≥ 2 * system.f + 1

end Beluga
end BlockSynchroniser
