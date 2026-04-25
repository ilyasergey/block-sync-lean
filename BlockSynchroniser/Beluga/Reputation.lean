/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Reputation mechanism (paper §4.2; pseudocode in Figure 8, Appendix E,
lines 23–32).
-/
import BlockSynchroniser.Beluga.BlockExt
import BlockSynchroniser.Beluga.State

namespace BlockSynchroniser
namespace Beluga

/--
Validators eligible for reputation increase from a batch of round-`r` blocks
(paper §4.2 reputation increase rule; Figure 8 lines 24–29).

`v_j` is a candidate iff at least `2f+1` of `blocks` carry a watermark
indicating `v_j`'s round `r-1` block was received: that is,
`B.watermark[j] = r - 1` for `≥ 2f+1` blocks `B`.
-/
def reputationIncreaseCandidates
    (system : BlockSynchroniserSystem)
    (blocks : List BelugaBlock) (r : Round) : List ValidatorId :=
  (List.range system.n).filter (fun j =>
    let attesting := blocks.filter (fun B => B.watermark[j]? = some (r - 1))
    attesting.length ≥ 2 * system.f + 1)

/--
`update_score_with_watermarks(r, B)` (paper Figure 8 lines 23–30).

Apply a `+1` reputation bump to every validator that the round-`r` block
batch attests has been kept up-to-date.
-/
def updateScoreWithWatermarks
    (system : BlockSynchroniserSystem)
    (rt : ReputationTable)
    (blocks : List BelugaBlock) (r : Round) : ReputationTable :=
  (reputationIncreaseCandidates system blocks r).foldl
    (fun rt' vid => rt'.incr vid) rt

/--
Reputation penalty `R_L` (paper §4.2 reputation decrease rule; Figure 8
lines 31–32).

Applied when: (i) `v_i` invokes the pull protocol to fetch a missing block
created by `v_j`, or (ii) `v_i` receives pull requests (blames) for a
`v_j`-authored block from at least `f+1` distinct validators.

Saturates at 0 (we use `Nat`-truncated subtraction).
-/
def reputationPenalty
    (rt : ReputationTable) (vid : ValidatorId) (R_L : Nat) : ReputationTable :=
  rt.decrBy vid R_L

/--
The reputation threshold `R_t := R_{2f+1} - R_L` (paper §4.2 admission
control). `R_{2f+1}` is the `(2f+1)`-th highest reputation across all
registered validators. A block creator's reputation must exceed `R_t` for
the block to be admissible (per the round-advancement rule (i) in §4.2).
-/
def reputationThreshold
    (system : BlockSynchroniserSystem)
    (rt : ReputationTable) (R_L : Nat) : Nat :=
  -- Sort scores in descending order, then take the (2f+1)-th element.
  let scores := system.validators.map (fun (vid, _) => rt.lookup vid)
  let sorted := scores.toArray.qsort (fun a b => decide (a > b)) |>.toList
  match sorted[2 * system.f]? with
  | some r => r - R_L
  | none   => 0

/-- True iff `vid`'s reputation in `rt` exceeds the threshold (paper §4.2
round-advancement rule (i)). -/
def aboveThreshold
    (system : BlockSynchroniserSystem)
    (rt : ReputationTable) (vid : ValidatorId) (R_L : Nat) : Prop :=
  rt.lookup vid > reputationThreshold system rt R_L

end Beluga
end BlockSynchroniser
