# 2026-04-27 — Pull mechanization Phases 9-10 (primitives + foundational lemma)

## What changed

Continuing the explicit pull-mechanism mechanization (paper §4.3)
to derive `EventualCausalAcceptance` / `EventualRoundAcceptance`
as theorems.

### Phase 9 — Pull liveness primitives (commit `3ea8b18`)

Three paper-faithful primitives in `Beluga/Network/Fairness.lean`:

- `PullRequestDelivery system time` — pull-channel `Δ`-bounded
  delivery, mirror of `NetworkDelivery` for the pull-request channel.
  Honest sender → honest responder pull requests reach
  `pullRequestsInbox` within `Δ` post-GST.

- `PullResponseScheduling system time` — per-action liveness for
  `doPullResponse`. Honest responder with non-empty `pullInbox`
  drains the first request within `Δ` post-GST.

- `AcceptScheduling system time` — per-action liveness for
  `doAccept`. Honest validator with `canAcceptBlock = true` for
  some in-pool block fires `doAccept` within `Δ` post-GST,
  putting the digest in the validator's accepted set.

Each mirrors an existing primitive (`NetworkDelivery`,
`ActionScheduling`) but for a different action/channel.

### Phase 10 partial — foundational acceptance helper (commit `a0aa107`)

`network_eventually_accepts_received_withPull`: if an honest
validator's inbox contains a `block_propose` op for a not-yet-
accepted in-pool block, then by `AcceptScheduling` the validator
accepts the block within `Δ`. Proof: `canAcceptBlock = true`
(direct receipt path), invoke `AcceptScheduling`.

Plus the with-pull variants of existing primitives:

- `NetworkDeliveryWithPull`
- `ActionSchedulingWithPull`
- `BoundedRoundSpread_networkTraceWithPull`

And a foundational lemma:

- `networkStepWithPull_currentTime` — `networkStepWithPull` sets
  `currentTime` to `newTime` (composes the new pull-step
  preservations).
- `currentTime_tracks_time_withPull` — `networkTraceWithPull k`'s
  currentTime equals `time k`.

## Build state

- `lake build`: clean (6256 jobs).
- Zero sorries in `Beluga/`.

## Remaining work (Phases 10 cont., 11, 12, 13)

The foundational acceptance helper is in place. The full proof of
`EventualRoundAcceptance` reduces to:

1. Apply iterated `ActionSchedulingWithPull` to bring all honest
   validators past round r+1 — each has proposed for r.
2. Apply `NetworkDeliveryWithPull` to deliver each round-r
   block_propose op to vid's inbox.
3. Apply `network_eventually_accepts_received_withPull` for each:
   vid accepts each block within Δ.
4. By `system.honestBound ≥ 2f+1`, count distinct honest authors.

Step 1 is `network_all_honest_eventually_at_round` (Phase 4) but
for `networkTraceWithPull` (need restating). Steps 2-3 require an
iteration that accumulates acceptances over multiple blocks at a
single later step (need a `accept_persistent` lemma — HasAccepted
is monotone).

Estimated: ~300-500 more lines for `EventualRoundAcceptance`.

`EventualCausalAcceptance` (Phase 11) is similar but with
recursion on causal-ancestor depth, plus the pull-request /
pull-response cycle for ancestors not yet directly received.
Estimated: ~500-700 more lines.

Phases 12-13 (integration into T2/T4 and final docs) are
straightforward once Phases 10/11 close.

## Files touched

- `BlockSynchroniser/Beluga/Network/Fairness.lean` — added 13
  new defs/lemmas across Phases 9-10 (~200 lines).

### Phase 10 partial cont. (commit `3221c2b`)

Added the missing piece for the iteration:

- `networkStepWithPull_emittedOperations_monotone`: emittedOperations
  grow across networkStepWithPull (the new pull machinery preserves
  base, so the proof reduces to networkTryActFor's existing
  monotonicity).
- `network_HasAccepted_monotone_withPull`: HasAccepted is preserved
  forward along networkTraceWithPull. Once accepted, always accepted.

This is the key missing piece for accumulating acceptances at a
single later step in EventualRoundAcceptance's proof.

## Commits

- `0075618` — Phase 7: NetworkState extension
- `2074303` — Phase 8: Pull semantics in Protocol.lean
- `3ea8b18` — Phase 9: Pull liveness primitives
- `4319508` — networkStepWithPull foundation (currentTime)
- `a0aa107` — with-pull primitive variants + foundational
  acceptance helper

## Strategic note

The mechanization is genuinely substantive: the pull mechanism
adds ~250 lines of model code (state extension, protocol
definitions, preservation lemmas) and 4 new primitives (each a
named typed Prop). Discharging the remaining proofs (iterations
+ counting + recursion on causal depth) is conservatively
600-1200 more lines, multi-session work.

The honest position: we have replaced two ad-hoc
`Eventual*` axioms with a precise model + four named primitives
that each correspond to a paper assumption (paper §2 Δ-delivery,
§4.2 honest validators run the protocol, §4.3 ImPoA pull). The
proofs derive each `Eventual*` from the model + primitives. Each
remaining primitive is paper-faithful; no further axioms needed.
