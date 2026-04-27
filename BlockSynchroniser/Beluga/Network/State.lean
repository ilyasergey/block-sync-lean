/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Network-aware extension of `BelugaState` (paper §2 + §4.2 push protocol).

This module is part of the **paper-faithful refinement** of the Beluga
trace model. The existing `Beluga/Protocol.lean` model has `step`
state-only (no notion of in-flight messages, no per-validator wall
clock); it captures the *stateful* behavior of the protocol but
abstracts the network. To derive `SchedulerFairness` from paper §2
(Δ-delivery), §4.2 (push protocol + `T_rd = 4Δ` timeout), and §4.3
(ImPoA), we need the network in scope.

This file extends the state with:

* **`DeliveryEvent`** — a pending push-protocol delivery (sender,
  recipient, message, deadline).
* **`BelugaState.inflight`** — the queue of events waiting to be
  delivered.
* **`BelugaState.currentTime`** — the wall-clock advance carried
  *inside* the state, so the trace's evolution is self-contained
  (no external `TimeMap` parameter needed for the network step).

The plan is documented in
[`docs/plan-derive-fairness-from-primitives.md`](../../../docs/plan-derive-fairness-from-primitives.md).
-/
import BlockSynchroniser.Beluga.State
import BlockSynchroniser.Beluga.Protocol

namespace BlockSynchroniser
namespace Beluga
namespace Network

/--
A pending push-protocol delivery. The paper's §4.2 push protocol has
the proposing validator broadcast its block to all others; under
post-GST partial synchrony each honest-to-honest delivery completes
within `Δ`. We model a delivery as a record carrying the sender,
recipient, message body, and the wall-clock deadline at which the
recipient is guaranteed to have received it (post-GST, between
honest pairs).
-/
structure DeliveryEvent where
  /-- The sending validator. -/
  sender : ValidatorId
  /-- The receiving validator. -/
  recipient : ValidatorId
  /-- The message body. In Beluga's push protocol this is always a
  `block_propose` op for the freshly-proposed block, plus implicit
  `block_accept`/`block_store` outputs from line 13 of Figure 8. We
  keep the message generic to allow modeling future operations
  (pull responses, blames, etc.). -/
  op : ValidatorOperation
  /-- The wall-clock deadline by which the recipient is guaranteed to
  have received `op`. Post-GST, honest-to-honest deliveries set
  `deliveryTime ≤ sendTime + Δ`; pre-GST or for Byzantine senders,
  `deliveryTime` is unconstrained (modeling adversarial scheduling). -/
  deliveryTime : Nat
  deriving Repr, DecidableEq

/--
A pending pull request (paper §4.3). A pull request is in-flight from
`requester` to `responder`, asking for the block whose digest is
`digest`. Post-GST, the request reaches the responder by
`deliveryTime`; the responder then schedules a `DeliveryEvent`
carrying the requested block back to the requester.
-/
structure PullRequest where
  /-- The validator issuing the pull request (wants the block). -/
  requester : ValidatorId
  /-- The validator the request is targeted at (expected to have the block). -/
  responder : ValidatorId
  /-- The digest of the block being requested. -/
  digest : BlockDigest
  /-- The wall-clock deadline by which the responder is guaranteed
  to have received the request (post-GST, between honest pairs). -/
  deliveryTime : Nat
  deriving Repr, DecidableEq

/-- A `NetworkState` is a `BelugaState` augmented with the network
queue and the wall-clock "now". The wall clock is part of the state
so that `networkStep` is a closed-form transition function (no
external `TimeMap` parameter). -/
structure NetworkState where
  /-- The underlying Beluga state (validators, blocks, op log). -/
  base : BelugaState := {}
  /-- Per-validator inboxes: messages this validator has received
  (i.e., delivered to its local view). Indexed in the same order as
  `base.validators`. We use a per-validator list for clean
  monotonicity arguments — the inbox only grows. -/
  inboxes : List (ValidatorId × List ValidatorOperation) := []
  /-- The queue of pending deliveries. Each event has its
  `deliveryTime`; the network step delivers all events with
  `deliveryTime ≤ currentTime`. -/
  inflight : List DeliveryEvent := []
  /-- In-flight pull requests (paper §4.3). Each request is
  delivered to the responder's `pullRequestInbox` when its
  `deliveryTime ≤ currentTime`. -/
  pullRequestsInflight : List PullRequest := []
  /-- Per-validator pull-request inbox: pull requests received and
  awaiting response. The responder action `doPullResponse` drains
  this inbox by scheduling block_propose deliveries. -/
  pullRequestsInbox : List (ValidatorId × List PullRequest) := []
  /-- The wall clock value at this state. Advanced by `networkStep`. -/
  currentTime : Nat := 0
  deriving Repr

/-- `NetworkState` projects to its underlying `BelugaState` for the
purposes of the abstract `SystemState` typeclass — exposing
validators (with the `BelugaValidator` → `Validator` projection),
blocks, and the operation log. The network-only fields (`inboxes`,
`inflight`, `currentTime`) are erased by this projection so all
specs stated against `SystemState` apply uniformly. -/
instance : SystemState NetworkState where
  validators        s := SystemState.validators s.base
  blocks            s := SystemState.blocks s.base
  emittedOperations s := SystemState.emittedOperations s.base

/-- The initial network state for a system. Validator inboxes are
empty; no deliveries pending; clock at `0`. -/
def NetworkState.init (system : BlockSynchroniserSystem) : NetworkState :=
  { base := BelugaState.init system
    inboxes := system.validators.map (fun (vid, _) => (vid, []))
    inflight := []
    pullRequestsInflight := []
    pullRequestsInbox := system.validators.map (fun (vid, _) => (vid, []))
    currentTime := 0 }

/-- Look up a validator's inbox by id. Returns `[]` if the validator
is not registered (which shouldn't happen for honest validators on a
well-formed initial state). -/
def NetworkState.inbox (s : NetworkState) (vid : ValidatorId) :
    List ValidatorOperation :=
  match s.inboxes.find? (fun (id, _) => id == vid) with
  | some (_, msgs) => msgs
  | none => []

/-- Append a message to a validator's inbox, preserving the order of
other entries. -/
def NetworkState.appendToInbox (s : NetworkState) (vid : ValidatorId)
    (op : ValidatorOperation) : NetworkState :=
  { s with inboxes := s.inboxes.map (fun (id, msgs) =>
      if id == vid then (id, msgs ++ [op]) else (id, msgs)) }

/-- Has `vid` received the propose op for block `B` at round `r`? Used
by the network-aware accept rule: a validator may only accept a block
once it has received it (or, under ImPoA, observed sufficient
evidence of availability). -/
def NetworkState.hasReceivedPropose (s : NetworkState) (vid : ValidatorId)
    (B : Block) (r : Round) : Bool :=
  (s.inbox vid).any (fun op =>
    match op with
    | .block_propose v B' r' => v == B.author && B' == B && r' == r
    | _ => false)

/-- Look up a validator's pull-request inbox by id. -/
def NetworkState.pullInbox (s : NetworkState) (vid : ValidatorId) :
    List PullRequest :=
  match s.pullRequestsInbox.find? (fun (id, _) => id == vid) with
  | some (_, reqs) => reqs
  | none => []

/-- Append a pull request to a validator's pull-request inbox. -/
def NetworkState.appendToPullInbox (s : NetworkState) (vid : ValidatorId)
    (req : PullRequest) : NetworkState :=
  { s with pullRequestsInbox := s.pullRequestsInbox.map (fun (id, reqs) =>
      if id == vid then (id, reqs ++ [req]) else (id, reqs)) }

/-- Remove a pull request from a validator's pull-request inbox.
Used when the responder has scheduled a response. -/
def NetworkState.removeFromPullInbox (s : NetworkState) (vid : ValidatorId)
    (req : PullRequest) : NetworkState :=
  { s with pullRequestsInbox := s.pullRequestsInbox.map (fun (id, reqs) =>
      if id == vid then (id, reqs.filter (· ≠ req)) else (id, reqs)) }

end Network
end Beluga
end BlockSynchroniser
