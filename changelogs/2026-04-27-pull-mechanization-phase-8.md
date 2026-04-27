# 2026-04-27 — Pull mechanism explicit modelization (Phase 8)

## What changed

The user requested full mechanization of the §4.3 pull mechanism so
that `EventualCausalAcceptance` and `EventualRoundAcceptance` (the
two paper-implicit liveness axioms used in T2/T4) can be proved as
theorems rather than assumed as Prop hypotheses.

This commit lands Phase 8 of that mechanization:

### `Beluga/Network/State.lean`

Extended `NetworkState` with pull bookkeeping:

- `PullRequest`: a pending pull request from `requester` to
  `responder` for a specific block `digest`, with a delivery deadline.
- `pullRequestsInflight : List PullRequest` — in-flight pull requests.
- `pullRequestsInbox : List (ValidatorId × List PullRequest)` —
  per-validator inbox of received pull requests awaiting response.
- Helpers: `pullInbox`, `appendToPullInbox`, `removeFromPullInbox`.

The new fields default to empty in `NetworkState.init`, so all
existing networkTrace/networkStep proofs continue to work unchanged.

### `Beluga/Network/Protocol.lean`

Added pull semantics:

- `deliverPullPending`: mirror of `deliverPending` for the pull
  channel — drains arrived pull requests from `pullRequestsInflight`
  to the responder's `pullRequestsInbox`.
- `doPullRequest system s vid d`: issue pull requests for digest
  `d` from `vid` to all registered validators with delivery deadline
  `currentTime + Δ`.
- `doPullResponse system s vid_resp req`: process one pull request
  in `vid_resp`'s inbox by scheduling a `block_propose`-carrying
  `DeliveryEvent` to the requester with delivery `currentTime + Δ`
  (if `vid_resp` has the block; otherwise just remove the request).
- `pullCandidate s vid`: find an in-pool block `vid` hasn't
  accepted, hasn't received, and hasn't already requested.
- `pullStepOne system s vid`: one validator's pull action (respond
  to first inbox request, else issue request for first candidate,
  else nop).
- `pullStep system s`: fold `pullStepOne` over all validators.
- `networkStepWithPull system s newTime`: alternate step function
  that calls `deliverPullPending` + `pullStep` before
  `networkTryActFor`. Keeps `networkStep` unchanged for backward
  compatibility with the existing §5 proofs.
- `networkTraceWithPull system time`: trace using the with-pull step.

### `Beluga/Network/Fairness.lean`

Added preservation lemmas for the new operations:

- `deliverPullPending` preserves `currentTime`, `base`, `inflight`,
  `inboxes` (only modifies `pullRequestsInflight` and
  `pullRequestsInbox`).
- `doPullRequest` and `doPullResponse` preserve `currentTime` and
  `base` (they only modify pull queues and `inflight`).
- `pullStepOne` and `pullStep` preserve `currentTime` and `base`
  (case-split on the action type).

## Build state

- `lake build`: clean (6256 jobs).
- Zero sorries in `Beluga/`.
- Pre-existing Mysticeti/Liveness.lean sorry unchanged (not part
  of this work).

## What's next (Phases 9–13)

- **Phase 9**: state pull liveness primitives:
  `PullRequestDelivery` (mirror of `NetworkDelivery` for pull
  requests), `PullResponseScheduling` (honest responders process
  pullInbox within Δ post-GST), `AcceptScheduling` (vid eventually
  accepts available blocks within Δ post-GST).
- **Phase 10**: prove `EventualRoundAcceptance` from primitives
  + the new model (apply ActionScheduling to get all honest
  proposing for round r; NetworkDelivery for the round-r blocks;
  AcceptScheduling for the accept actions; count to 2f+1).
- **Phase 11**: prove `EventualCausalAcceptance` from primitives
  + the new model (recursion on causal ancestors; for each ancestor
  not yet accepted, the global pool guarantees it's there;
  pullCandidate triggers a pull; PullRequestDelivery delivers the
  request; PullResponseScheduling triggers the response;
  NetworkDelivery delivers the response; AcceptScheduling fires the
  accept).
- **Phase 12**: update T2/T4 in `Beluga/Network/Theorems.lean` to
  use the proved versions; remove the `Eventual*` hypotheses.
- **Phase 13**: final docs sync; cleanup the `networkTrace` /
  `networkTraceWithPull` parallel paths (decide whether to keep
  both or unify under the with-pull version).

## Files touched

- `BlockSynchroniser/Beluga/Network/State.lean` — pull state
  extension (commit `0075618`).
- `BlockSynchroniser/Beluga/Network/Protocol.lean` — pull
  definitions (commit `2074303`).
- `BlockSynchroniser/Beluga/Network/Fairness.lean` — preservation
  lemmas (commit `2074303`).
