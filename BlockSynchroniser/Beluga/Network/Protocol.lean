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
    -- Schedule push deliveries: the proposed block is pushed to every
    -- registered validator with deadline `currentTime + Δ`. The
    -- newly emitted op is the last one in `s_proposed.emittedOperations`.
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
          let bv' : BelugaValidator :=
            { bv with currentRound := r + 1, roundEntryTime := s.currentTime }
          let base' : BelugaState := doAdvance s.base vid
          -- Update the validator's roundEntryTime in the new base.
          let base'' : BelugaState := { base' with
            validators := base'.validators.map (fun (id, bv0) =>
              if id == vid then (id, bv') else (id, bv0)) }
          some { s with base := base'' }
        else none

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

/-- The Beluga **network-aware** trace: state at step `n` is obtained
by iterating `networkStep` from `NetworkState.init system` with the
wall-clock advance dictated by `time`. Each step takes `time (n+1)`
as its `newTime`. -/
def networkTrace (system : BlockSynchroniserSystem) (time : Nat → Nat) :
    Trace NetworkState :=
  fun n => Nat.rec (motive := fun _ => NetworkState)
    { NetworkState.init system with currentTime := time 0 }
    (fun i s => networkStep system s (time (i + 1))) n

end Network
end Beluga
end BlockSynchroniser
