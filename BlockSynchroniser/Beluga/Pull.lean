/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

ImPoA-based hybrid pull (paper §4.3).
-/
import BlockSynchroniser.Block
import BlockSynchroniser.System
import BlockSynchroniser.State
import BlockSynchroniser.Trace
import BlockSynchroniser.Beluga.State

namespace BlockSynchroniser
namespace Beluga

/--
**Implicit Proof-of-Availability** (paper §4.3.1).

A block `B` is *implicitly available* if at least `f + 1` distinct validators
have authored blocks in subsequent rounds (`B'.r > B.r`) that reference `B`
as a parent. The paper allows weak links to count as well; we take the
strong-link-only lower bound here.

The point: `f + 1` references guarantees at least one *honest* author has
attested to `B`'s availability (since at most `f` are Byzantine), so the
validator can safely accept `B` based on the implicit attestation rather
than having to pull `B`'s ancestors first.
-/
def implicitlyAvailable {S} [SystemState S]
    (system : BlockSynchroniserSystem) (state : S) (B : Block) : Prop :=
  let refs :=
    ((SystemState.blocks state).filter (fun B' =>
      decide (B'.r > B.r) && B'.parents.contains B.d)).map (·.author)
  refs.eraseDups.length ≥ system.f + 1

/-- Bool-valued version of `implicitlyAvailable`. -/
def implicitlyAvailableB {S} [SystemState S]
    (system : BlockSynchroniserSystem) (state : S) (B : Block) : Bool :=
  let refs :=
    ((SystemState.blocks state).filter (fun B' =>
      decide (B'.r > B.r) && B'.parents.contains B.d)).map (·.author)
  decide (refs.eraseDups.length ≥ system.f + 1)

/--
**Live-block classification** (paper §4.3.2 live module).

Missing blocks are *live* if they belong to the most recent rounds where
they could still affect quorum formation for the validator's current round
advancement; otherwise *bulk*. The paper's precise definition depends on
parent-availability state (whether each parent is proven-available); we
approximate here by treating any block at or beyond `currentRound - 1` as
live.

Live blocks are pulled deterministically (broadcast to all validators) so
they're guaranteed to land within one round-trip; bulk blocks use a
randomized pull (out of scope — the random-pull complexity bound is a
probabilistic claim not formalized here).
-/
def isLive (currentRound : Round) (B : Block) : Prop :=
  B.r ≥ currentRound - 1

/-- Bool version of `isLive`. -/
def isLiveB (currentRound : Round) (B : Block) : Bool :=
  decide (B.r ≥ currentRound - 1)

/-- Bulk-block classification — complement of live. -/
def isBulk (currentRound : Round) (B : Block) : Prop :=
  ¬ isLive currentRound B

/--
Partition a list of missing-block digests into live and bulk, given the
validator's current round.

This corresponds to the bulk/live split that drives the hybrid pull
strategy in paper §4.3.2 (Figure 3(c)).
-/
def classifyMissing {S} [SystemState S]
    (state : S) (currentRound : Round) (missing : List BlockDigest) :
    List BlockDigest × List BlockDigest :=
  let liveDigests :=
    missing.filter (fun d =>
      match getBlockByDigest state d with
      | some B => isLiveB currentRound B
      | none   => false)
  let bulkDigests :=
    missing.filter (fun d =>
      match getBlockByDigest state d with
      | some B => ¬ isLiveB currentRound B
      | none   => true)  -- unknown blocks treated as bulk by default
  (liveDigests, bulkDigests)

/--
Acceptable-via-ImPoA predicate (paper §4.3.1, expanded version of
`AdmissionControl.isAcceptable`).

A block is acceptable for `vid` if either (a) `vid` has output
`block_accept` for it (the strict §4.2 condition), or (b) the block is
implicitly available, in which case `vid` can accept it without having
synchronized its missing causal history first.
-/
def isAcceptableImPoA {S} [SystemState S]
    (system : BlockSynchroniserSystem) (state : S)
    (vid : ValidatorId) (B : Block) : Prop :=
  HasAccepted state vid B.d ∨ implicitlyAvailable system state B

end Beluga
end BlockSynchroniser
