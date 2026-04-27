/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Network-aware protocol step (paper §4.2 push protocol + §4.3 ImPoA
hybrid pull, plus the per-round timeout `T_rd = 4Δ`).

This module implements `networkStep` and `networkTrace`, the
paper-faithful refinement of `step` / `belugaTrace` from
[`Protocol.lean`](../Protocol.lean). The refinement adds four
orthogonal pieces:

1. **Delivery** — events in `inflight` with
   `deliveryTime ≤ currentTime` are moved into the recipient's inbox
   before any `tryActFor` decision.
2. **Push** — `networkDoPropose` schedules `DeliveryEvent`s for every
   other validator with `deliveryTime ≤ currentTime + Δ` (post-GST,
   honest senders) or unconstrained (pre-GST or Byzantine).
3. **Timeout** — the round-advance branch of `networkTryActFor` fires
   either under the existing `allProposedFor` gate *or* if
   `currentTime ≥ bv.roundEntryTime + 4Δ`.
4. **ImPoA accept** — the accept rule allows a validator to accept
   `B` if all parents are accepted *or* if the parents are
   implicitly available (referenced by f+1 subsequent in-pool blocks).

The plan is in
[`docs/plan-derive-fairness-from-primitives.md`](../../../docs/plan-derive-fairness-from-primitives.md).
-/
import BlockSynchroniser.Beluga.Protocol
import BlockSynchroniser.Beluga.Network.State

namespace BlockSynchroniser
namespace Beluga
namespace Network

open Beluga (BelugaState BelugaValidator)

/-! ## Delivery semantics

`deliverPending` moves every event in `inflight` with
`deliveryTime ≤ currentTime` into the recipient's inbox; events
that are not yet due remain in `inflight`. Order of delivery
follows the order in `inflight`, giving a deterministic step. -/

/-- Move every event in `inflight` whose `deliveryTime ≤ s.currentTime`
into the recipient's inbox; remove them from `inflight`. -/
def NetworkState.deliverPending (s : NetworkState) : NetworkState :=
  let (toDeliver, stillInflight) :=
    s.inflight.partition (fun e => e.deliveryTime ≤ s.currentTime)
  let s' : NetworkState := { s with inflight := stillInflight }
  toDeliver.foldl (fun acc e => acc.appendToInbox e.recipient e.op) s'

/-- Move every pull request in `pullRequestsInflight` whose
`deliveryTime ≤ s.currentTime` into the responder's
`pullRequestsInbox`. Mirrors `deliverPending` for the pull channel
(paper §4.3). -/
def NetworkState.deliverPullPending (s : NetworkState) : NetworkState :=
  let (toDeliver, stillInflight) :=
    s.pullRequestsInflight.partition (fun r => r.deliveryTime ≤ s.currentTime)
  let s' : NetworkState := { s with pullRequestsInflight := stillInflight }
  toDeliver.foldl (fun acc r => acc.appendToPullInbox r.responder r) s'

/-! ## ImPoA: implicit availability

A block `B` is *implicitly available* in `s` if at least `f+1`
subsequent in-pool blocks reference it (paper §4.3). This is the
structural property that lets a validator accept `B` without having
directly received `B`'s parents. -/

/-- True iff `B`'s digest appears in the parent set of at least `f+1`
blocks currently in `s.base.blocks`. -/
def NetworkState.implicitlyAvailable (s : NetworkState) (system : BlockSynchroniserSystem)
    (B : Block) : Bool :=
  decide ((s.base.blocks.filter (fun B' => B.d ∈ B'.parents)).length ≥ system.f + 1)

/-- True iff every digest in `B.parents` corresponds to a block in
`s.base.blocks` whose digest is implicitly available, *or* is
already accepted by `vid`. This is the more permissive accept gate
of the network-aware protocol — accept `B` whenever its parents are
either explicitly accepted or implicitly available via f+1
references. -/
def NetworkState.parentsAcceptableImPoA (s : NetworkState)
    (system : BlockSynchroniserSystem) (vid : ValidatorId) (B : Block) : Bool :=
  B.parents.all (fun pd =>
    hasAcceptedDigest s.base vid pd ||
    -- Implicit availability: pd is the digest of some block whose
    -- f+1-references are met.
    (s.base.blocks.any (fun Bp =>
      Bp.d == pd && decide ((s.base.blocks.filter (fun B' => Bp.d ∈ B'.parents)).length ≥ system.f + 1))))

/-! ## Per-validator timeout

A validator `vid` at round `r` with `roundEntryTime = t_r` may
advance to round `r + 1` if either:
- `allProposedFor system s.base r = true` (every registered validator
  has proposed for `r` — the paper's quorum-style gate), or
- `s.currentTime ≥ t_r + 4 * system.Δ` (the per-round timeout
  `T_rd = 4Δ` from paper §4.2 has fired).
-/

/-- True iff the per-round timeout has fired for validator `bv` at the
state's current wall clock. -/
def NetworkState.timeoutFired (s : NetworkState) (system : BlockSynchroniserSystem)
    (bv : BelugaValidator) : Bool :=
  decide (s.currentTime ≥ bv.roundEntryTime + 4 * system.Δ)

/-! ## Pull actions (paper §4.3 explicit handshake)

When a validator notices a block in the pool it hasn't received and
hasn't accepted, it issues a pull request to all other validators.
The request travels via `pullRequestsInflight` (delivered by
`deliverPullPending` after Δ post-GST) and lands in each responder's
`pullRequestsInbox`. Responders that have the block schedule a
`block_propose`-carrying `DeliveryEvent` back to the requester.

The two new actions are:
- `doPullRequest`: issue requests for a missing block.
- `doPullResponse`: process one pull request from the inbox by
  scheduling a block_propose delivery (if the responder has the
  block). -/

/-- Schedule pull requests for digest `d` from `vid` to every
registered validator, with delivery deadline `currentTime + Δ`. -/
def doPullRequest (system : BlockSynchroniserSystem) (s : NetworkState)
    (vid : ValidatorId) (d : BlockDigest) : NetworkState :=
  let requests : List PullRequest := system.validators.map (fun (responder, _) =>
    { requester := vid, responder := responder, digest := d,
      deliveryTime := s.currentTime + system.Δ })
  { s with pullRequestsInflight := s.pullRequestsInflight ++ requests }

/-- Process one pull request: if `vid_resp` has the block matching
`req.digest`, schedule a `block_propose` delivery to `req.requester`
with deadline `currentTime + Δ`. Either way, remove the request
from the responder's inbox. -/
def doPullResponse (system : BlockSynchroniserSystem) (s : NetworkState)
    (vid_resp : ValidatorId) (req : PullRequest) : NetworkState :=
  match s.base.blocks.find? (fun B => B.d == req.digest) with
  | some B =>
    let op := ValidatorOperation.block_propose B.author B B.r
    let ev : DeliveryEvent :=
      { sender := vid_resp, recipient := req.requester, op := op,
        deliveryTime := s.currentTime + system.Δ }
    let s' : NetworkState := { s with inflight := s.inflight ++ [ev] }
    s'.removeFromPullInbox vid_resp req
  | none =>
    s.removeFromPullInbox vid_resp req

/-- A pull-request candidate digest for `vid`: an in-pool block that
`vid` hasn't accepted, hasn't received via push, AND for which `vid`
hasn't already issued a pull. -/
def NetworkState.pullCandidate (s : NetworkState) (vid : ValidatorId) : Option Block :=
  s.base.blocks.find? (fun B =>
    !hasAcceptedDigest s.base vid B.d &&
    !s.hasReceivedPropose vid B B.r &&
    !s.pullRequestsInflight.any (fun r => r.requester == vid && r.digest == B.d))

/-! ## Network-aware action: `networkTryActFor`

Mirrors the paper's Figure 8 priority order, but with the ImPoA-aware
accept rule and the timeout-augmented advance branch. The action
uses the validator's *inbox* (not the global pool) to decide
acceptance: a block can only be accepted once it has been received
or implicitly availability-verified. -/

/-- A validator can accept block `B` if (i) `B` is known (in the
state's pool) and `vid` has not yet accepted it, and (ii) either
`vid` has received `B`'s propose op (push delivery) or `B`'s
parents are all accepted-or-implicitly-available. -/
def NetworkState.canAcceptBlock (s : NetworkState) (system : BlockSynchroniserSystem)
    (vid : ValidatorId) (B : Block) : Bool :=
  !hasAcceptedDigest s.base vid B.d &&
  (s.hasReceivedPropose vid B B.r || s.parentsAcceptableImPoA system vid B)

/-- Network-aware variant of `tryActFor`. -/
def networkTryActFor (system : BlockSynchroniserSystem) (s : NetworkState)
    (vid : ValidatorId) (bv : BelugaValidator) : Option NetworkState :=
  let r := bv.currentRound
  -- 1. Propose if not yet for current round
  if !hasProposedFor s.base vid r then
    let s_proposed : BelugaState := doPropose system s.base vid r
    let newOp := ValidatorOperation.block_propose vid
      { r := r, author := vid, d := digest system r vid
        parents := if r = 0 then [] else
          (s.base.blocks.filter (fun B => B.r == r - 1)).map (·.d)
        payload := [] } r
    let newDeliveries : List DeliveryEvent :=
      system.validators.map (fun (recipient, _) =>
        { sender := vid, recipient := recipient, op := newOp,
          deliveryTime := s.currentTime + system.Δ })
    some { s with base := s_proposed, inflight := s.inflight ++ newDeliveries }
  else
    -- 2. Accept any acceptable block (network-aware gate)
    match s.base.blocks.find? (fun B => s.canAcceptBlock system vid B) with
    | some B => some { s with base := doAccept s.base vid B }
    | none =>
      -- 3. Store any accepted-but-not-stored block
      match s.base.blocks.find? (fun B =>
              hasAcceptedDigest s.base vid B.d && !hasStoredDigest s.base vid B.d) with
      | some B => some { s with base := doStore s.base vid B }
      | none =>
        -- 4. Advance round if quorum gate fires OR timeout has fired
        if allProposedFor system s.base r || s.timeoutFired system bv then
          some { s with base := updateValidator s.base vid (fun bv0 =>
            { bv0 with currentRound := bv0.currentRound + 1,
                       roundEntryTime := s.currentTime }) }
        else none

/-! ## `pullStep`: pull request issuance and response

Pull is modeled as a separate, additive step that runs in
`networkStep` BEFORE `networkTryActFor`. This keeps the existing
`networkTryActFor` invariant proofs unchanged: pull only modifies
`pullRequestsInflight`, `pullRequestsInbox`, and `inflight`
(adding response events). It never modifies `base`, `inboxes`,
or `currentTime`. -/

/-- One pull action by validator `vid`: respond to a pending pull
request if any, else issue a pull request for a missing block if any. -/
def pullStepOne (system : BlockSynchroniserSystem) (s : NetworkState)
    (vid : ValidatorId) : NetworkState :=
  match s.pullInbox vid with
  | req :: _ => doPullResponse system s vid req
  | [] =>
    match s.pullCandidate vid with
    | some B => doPullRequest system s vid B.d
    | none => s

/-- For each validator, do one pull action. Folded over `system.validators`. -/
def pullStep (system : BlockSynchroniserSystem) (s : NetworkState) : NetworkState :=
  system.validators.foldl (fun acc (vid, _) => pullStepOne system acc vid) s

/-! ## Network-aware step

`networkStep system s newTime` advances the wall clock to `newTime`,
delivers any events whose `deliveryTime ≤ newTime`, and then runs
the first applicable `networkTryActFor` over the validator list. -/

/-- One step of the network-aware Beluga protocol. -/
def networkStep (system : BlockSynchroniserSystem) (s : NetworkState)
    (newTime : Nat) : NetworkState :=
  -- 1. Advance the wall clock.
  let s_advanced : NetworkState := { s with currentTime := newTime }
  -- 2. Deliver events whose deadline has passed.
  let s_delivered : NetworkState := s_advanced.deliverPending
  -- 3. Run the first applicable validator action.
  match s_delivered.base.validators.findSome?
      (fun (vid, bv) => networkTryActFor system s_delivered vid bv) with
  | some s' => s'
  | none    => s_delivered

/-- One step of the network-aware Beluga protocol, with the explicit
pull mechanism (paper §4.3) layered on top. Used by `networkTraceWithPull`
to derive `EventualCausalAcceptance` / `EventualRoundAcceptance` as
theorems. -/
def networkStepWithPull (system : BlockSynchroniserSystem) (s : NetworkState)
    (newTime : Nat) : NetworkState :=
  let s_advanced : NetworkState := { s with currentTime := newTime }
  let s_delivered : NetworkState := s_advanced.deliverPending
  let s_pull_delivered : NetworkState := s_delivered.deliverPullPending
  let s_pulled : NetworkState := pullStep system s_pull_delivered
  match s_pulled.base.validators.findSome?
      (fun (vid, bv) => networkTryActFor system s_pulled vid bv) with
  | some s' => s'
  | none    => s_pulled

/-- The Beluga **network-aware** trace: state at step `n` is obtained
by iterating `networkStep` from `NetworkState.init system` with the
wall-clock advance dictated by `time`. Each step takes `time (n+1)`
as its `newTime`. -/
def networkTrace (system : BlockSynchroniserSystem) (time : Nat → Nat) :
    Trace NetworkState :=
  fun n => Nat.rec (motive := fun _ => NetworkState)
    { NetworkState.init system with currentTime := time 0 }
    (fun i s => networkStep system s (time (i + 1))) n

/-- The Beluga network-aware trace WITH the explicit pull mechanism.
Used to prove `EventualCausalAcceptance` and `EventualRoundAcceptance`
as theorems. -/
def networkTraceWithPull (system : BlockSynchroniserSystem) (time : Nat → Nat) :
    Trace NetworkState :=
  fun n => Nat.rec (motive := fun _ => NetworkState)
    { NetworkState.init system with currentTime := time 0 }
    (fun i s => networkStepWithPull system s (time (i + 1))) n

end Network
end Beluga
end BlockSynchroniser
