# 2026-04-26 — Phases A–D: network-aware Beluga model (definitions)

Per the plan in
[`docs/plan-derive-fairness-from-primitives.md`](../docs/plan-derive-fairness-from-primitives.md),
this commit introduces the **network-aware** refinement of the
Beluga trace model — definitions only. Phase E (the derivation of
`SchedulerFairness` as a *theorem*) builds on these definitions in
the next commit.

## What changed

### Phase A — per-validator time tracking

Added field `roundEntryTime : Nat` (default `0`) to `BelugaValidator`
in [`Beluga/State.lean`](../BlockSynchroniser/Beluga/State.lean).
Records the wall-clock at which the validator entered its
`currentRound`. Used by the `T_rd = 4Δ` per-round timeout (paper
§4.2) in Phase C. Default-valued so the existing model (which never
reads or writes the field) continues to work.

### Phase B — In-flight messages + delivery

New module
[`Beluga/Network/State.lean`](../BlockSynchroniser/Beluga/Network/State.lean):

- **`DeliveryEvent`** — pending push-protocol delivery
  `{sender, recipient, op, deliveryTime}`.
- **`NetworkState`** — wraps a `BelugaState` with `inboxes`
  (per-validator received messages), `inflight`
  (queued deliveries), and `currentTime` (wall clock).
- `NetworkState.deliverPending` moves due events from `inflight`
  to recipient inboxes.
- `NetworkState.hasReceivedPropose` — has `vid` received the propose
  op for block `B` at round `r`?
- `SystemState NetworkState` instance projects to the underlying
  `BelugaState`'s validators / blocks / op-log, so all
  `SystemState`-level specs apply uniformly.

### Phase C — `T_rd = 4Δ` timeout branch

In
[`Beluga/Network/Protocol.lean`](../BlockSynchroniser/Beluga/Network/Protocol.lean):

- `NetworkState.timeoutFired` — `currentTime ≥ bv.roundEntryTime + 4Δ`.
- `networkTryActFor`'s round-advance branch fires under
  `allProposedFor ∨ timeoutFired`, matching paper §4.2's "either
  receive 2f+1 acceptable round-`r-1` blocks **or** the per-round
  timeout `T_rd` expires" rule.
- Round-advance updates `roundEntryTime := currentTime` for the
  advancing validator.

### Phase D — ImPoA-based accept rule

In `Beluga/Network/Protocol.lean`:

- `NetworkState.implicitlyAvailable` — block `B` has its digest
  referenced by ≥ `f+1` blocks in the pool (paper §4.3).
- `NetworkState.parentsAcceptableImPoA` — every parent digest is
  either accepted by `vid` *or* implicitly available.
- `NetworkState.canAcceptBlock` — `vid` may accept `B` if not
  already accepted, AND (`vid` has received `B`'s propose op via
  the push protocol, OR `B`'s parents are acceptable under ImPoA).
- The accept branch of `networkTryActFor` uses this richer gate.

### `networkStep` and `networkTrace`

- `networkStep system s newTime` advances the wall clock to
  `newTime`, calls `deliverPending` to flush due events, then runs
  the first applicable `networkTryActFor`. Closed-form transition
  (no external inputs apart from the new time).
- `networkTrace system time` is the iterated trace from
  `NetworkState.init system`, with each step taking `time (n+1)` as
  its `newTime`.

## Build state

`lake build` clean. **Beluga/Theorems.lean: 0 sorries** (unchanged).
The new network-aware definitions in `Beluga/Network/` are
self-contained and don't yet wire into Theorems.lean — that's
Phase F.

## What's next

- **Phase E** — define `NetworkDelivery` axiom and derive
  `schedulerFairness_holds` as a theorem about `networkTrace`.
  ~7 days, ~600–1000 lines.
- **Phase F** — migrate Theorems.lean: §5 wrappers take
  `NetworkDelivery` (paper-stated primitive) instead of
  `SchedulerFairness` (axiom we previously surfaced).

After Phase F, every paper §5 main theorem will take only
paper-stated assumptions.
