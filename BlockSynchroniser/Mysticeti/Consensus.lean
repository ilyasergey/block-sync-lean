/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Mysticeti consensus rules layered on top of Beluga (paper Appendix D.1).

Mysticeti orders transactions on top of the DAG constructed by Beluga
using a two-step scheme: (1) decide the status of leader blocks
(`ToCommit` / `ToSkip`); (2) order all leader blocks decided as
`ToCommit` and their causal-history blocks via a deterministic
linearization. We formalize the decision-rule layer here.
-/
import BlockSynchroniser.Block
import BlockSynchroniser.System
import BlockSynchroniser.State
import BlockSynchroniser.Beluga.Patterns

namespace BlockSynchroniser
namespace Mysticeti

/--
Round-robin leader schedule (paper Appendix D.1.2): leader of round `r`
is `r mod n`. Single-leader version (the paper considers single-leader
when building Mysticeti-Beluga).
-/
def leaderOf (system : BlockSynchroniserSystem) (r : Round) : ValidatorId :=
  r % system.n

/-- True iff `B` is the round-`r` leader block — i.e., authored by the
designated leader for round `r`. -/
def isLeaderBlock (system : BlockSynchroniserSystem) (B : Block) : Prop :=
  B.author = leaderOf system B.r

/-! ## DAG patterns on leader blocks (paper Appendix D.1.1) -/

/--
**Skip pattern** (paper Appendix D.1.1): leader block `B_L` is *not*
referenced by `2f+1` blocks of the *successive* round (round `B.r + 1`).

Equivalently: fewer than `2f+1` round-`(B.r+1)` blocks include `B_L.d`
in their parents.
-/
def skipPattern (system : BlockSynchroniserSystem) {S} [SystemState S]
    (state : S) (B : Block) : Prop :=
  let nextRound :=
    (SystemState.blocks state).filter (fun B' =>
      B'.r == B.r + 1 && B'.parents.contains B.d)
  nextRound.length < 2 * system.f + 1

/-- Bool-valued `skipPattern`. -/
def skipPatternB (system : BlockSynchroniserSystem) {S} [SystemState S]
    (state : S) (B : Block) : Bool :=
  let nextRound :=
    (SystemState.blocks state).filter (fun B' =>
      B'.r == B.r + 1 && B'.parents.contains B.d)
  decide (nextRound.length < 2 * system.f + 1)

/--
**Certificate pattern at round `B.r + 1`** (paper Appendix D.1.1
footnote 6 — same as §4.4 certificate pattern, restricted to the next
round).
-/
def certificatePatternAt (system : BlockSynchroniserSystem) {S} [SystemState S]
    (state : S) (B : Block) (atRound : Round) : Prop :=
  let referencers :=
    (SystemState.blocks state).filter (fun B' =>
      B'.r == atRound && B'.parents.contains B.d)
  let distinctAuthors := referencers.map (·.author) |>.eraseDups
  distinctAuthors.length ≥ 2 * system.f + 1

/-- Bool-valued `certificatePatternAt`. -/
def certificatePatternAtB (system : BlockSynchroniserSystem) {S} [SystemState S]
    (state : S) (B : Block) (atRound : Round) : Bool :=
  let referencers :=
    (SystemState.blocks state).filter (fun B' =>
      B'.r == atRound && B'.parents.contains B.d)
  let distinctAuthors := referencers.map (·.author) |>.eraseDups
  decide (distinctAuthors.length ≥ 2 * system.f + 1)

/-! ## Decision rules (paper Appendix D.1.1) -/

/-- Decision status of a leader block. -/
inductive Decision
  | ToCommit
  | ToSkip
  | Undecided
  deriving Repr, DecidableEq

/--
**Direct decision rule** (paper Appendix D.1.1):

A round-`r` leader block `B_L^r` is *directly decided* if:
* (i) at least `2f+1` certificate patterns exist for `B_L^r` at round
      `r+2` — `B_L^r` is decided `ToCommit`; **or**
* (ii) `B_L^r` is a skip pattern — `B_L^r` is decided `ToSkip`.

Otherwise it remains `Undecided` and the indirect rule applies.
-/
def directDecide (system : BlockSynchroniserSystem) {S} [SystemState S]
    (state : S) (B : Block) : Decision :=
  if certificatePatternAtB system state B (B.r + 2) then Decision.ToCommit
  else if skipPatternB system state B then Decision.ToSkip
  else Decision.Undecided

/--
**Indirect decision rule** (paper Appendix D.1.1):

For any undecided round-`r'` leader block `B_L^{r'}`, search for the
first subsequent leader block `B_L^{r''}` (`r'' > r' + 2`) that is
either decided `ToCommit` or still `Undecided`:
* If `B_L^{r''}` is `ToCommit` and causally references a certificate for
  `B_L^{r'}` ⇒ `B_L^{r'}` is `ToCommit`.
* If `B_L^{r''}` is `ToCommit` and does *not* causally reference such a
  certificate ⇒ `B_L^{r'}` is `ToSkip`.
* If `B_L^{r''}` is `Undecided` ⇒ `B_L^{r'}` remains `Undecided` for
  now.

The full indirect rule needs the recursive search; we capture only the
"one-step lookahead" approximation here. The recursive variant lives in
the safety proof.
-/
def indirectDecideStep (laterDecision : Decision) (laterReferencesCert : Bool) : Decision :=
  match laterDecision with
  | Decision.ToCommit =>
      if laterReferencesCert then Decision.ToCommit else Decision.ToSkip
  | _ => Decision.Undecided

/-! ## Consensus view and transaction order

Per-validator consensus state. In a fully-modeled execution this would
live inside each validator's local view of the trace; we expose it
abstractly here so the safety/liveness lemmas can be stated precisely
without forcing all of `BelugaState` to carry consensus-specific data.

A `ConsensusView` records, for each validator, what `Decision` it has
assigned to each leader block (identified by its digest). A
`TransactionOrder` records each validator's local sequence of
transactions delivered by the consensus layer.

Lemmas in `Mysticeti/Safety.lean` and `Mysticeti/Liveness.lean` take
these as parameters and constrain them to be derived from the
underlying state in the obvious way. The full integration with
`BelugaState` is a follow-up phase.
-/

/-- Each validator's `Decision` for each leader-block digest. -/
abbrev ConsensusView := ValidatorId → BlockDigest → Decision

/-- Each validator's locally-ordered transaction stream. -/
abbrev TransactionOrder := ValidatorId → List Transaction

/--
A `ConsensusView` is *consistent* across honest validators if no two
honest validators assign conflicting non-`Undecided` decisions to the
same leader block. (Captures: "no honest validator commits while
another skips.")
-/
def ConsensusView.Consistent (system : BlockSynchroniserSystem)
    (view : ConsensusView) : Prop :=
  ∀ d vid₁ vid₂,
    isHonestValidator system vid₁ = true →
    isHonestValidator system vid₂ = true →
    view vid₁ d ≠ Decision.Undecided →
    view vid₂ d ≠ Decision.Undecided →
    view vid₁ d = view vid₂ d

/--
Two transaction orders are *consistent* if one is a prefix of the
other (so they agree on the common prefix and grow monotonically).
-/
def TransactionOrder.Consistent (system : BlockSynchroniserSystem)
    (order : TransactionOrder) : Prop :=
  ∀ vid₁ vid₂,
    isHonestValidator system vid₁ = true →
    isHonestValidator system vid₂ = true →
    (order vid₁).isPrefixOf (order vid₂) = true ∨
    (order vid₂).isPrefixOf (order vid₁) = true

end Mysticeti
end BlockSynchroniser
