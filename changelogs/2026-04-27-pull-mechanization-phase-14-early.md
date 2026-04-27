# 2026-04-27 — Phase 14 (early): bundle six paper primitives

## What changed

Originally planned as Phase 14 (post-Phases 10–13), pulled forward
on user request to simplify the calling convention before the
remaining proofs land.

### `Beluga/Network/Fairness.lean`

Defines the `PartiallySynchronousFairness` record bundling the six
paper-named primitives that discharge the §5 theorems:

```lean
structure PartiallySynchronousFairness
    (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop where
  /-- Paper §2 Δ-bounded honest-honest block_propose delivery. -/
  networkDelivery        : NetworkDelivery system time
  /-- Paper §4.2 per-validator round-advance liveness. -/
  actionScheduling       : ActionScheduling system time
  /-- F-1b gap-1 invariant on the round spread between honest
      validators. -/
  boundedRoundSpread     : BoundedRoundSpread_networkTrace system time
  /-- Paper §4.2 per-action liveness for the accept action. -/
  acceptScheduling       : AcceptScheduling system time
  /-- Paper §4.3 pull-channel Δ-delivery. -/
  pullRequestDelivery    : PullRequestDelivery system time
  /-- Paper §4.3 pull-response action liveness. -/
  pullResponseScheduling : PullResponseScheduling system time
```

This is the symmetric mirror of the existing conclusion-side
`BelugaPostGSTLiveness` bundle. One named hypothesis per
paper-stated assumption.

### `Beluga/Network/Theorems.lean`

Refactored §5 wrappers to take the bundle:

| Wrapper | Old hypotheses | New hypothesis |
|---|---|---|
| `network_lemma1_honest_round_entry` | `h_delivery`, `h_scheduling`, `h_spread` | `h_prim` |
| `network_lemma2_round_latency` | same | same |
| `network_theorem1_block_availability` | same | same |
| `network_theorem3_round_progression` | same | same |
| `networkTrace_isBlockSynchronizer` | same + `h_eventual_*` | `h_prim` + `h_eventual_*` |

Internal proof bodies destructure the bundle fields as needed
(`h_prim.networkDelivery`, `h_prim.actionScheduling`,
`h_prim.boundedRoundSpread`).

`network_theorem2_causal_availability` and
`network_theorem4_round_termination` still take their individual
`Eventual*` hypotheses pending Phases 10–11 (which will replace
them with proofs that consume `h_prim.acceptScheduling`,
`h_prim.pullRequestDelivery`, `h_prim.pullResponseScheduling`).

## Why pulled forward

The user's reasoning: simplify the calling convention BEFORE the
remaining proofs land. The Phase 10/11 proofs will destructure
`h_prim` the same way the existing wrappers do, so the bundle's
shape doesn't depend on what those proofs end up needing.

## Alternative considered

Group by paper section (`NetworkChannelDelivery`,
`ProtocolFairness`, plus a standalone `BoundedRoundSpread`): more
paper-faithful structurally but more boilerplate and less
alignment with the existing single-bundle `BelugaPostGSTLiveness`
pattern. We chose the single-bundle approach for symmetry.

## Build state

- `lake build`: clean (6256 jobs).
- Zero sorries in `Beluga/`.

## Files touched

- `BlockSynchroniser/Beluga/Network/Fairness.lean` —
  `PartiallySynchronousFairness` record (~20 lines).
- `BlockSynchroniser/Beluga/Network/Theorems.lean` — §5 wrapper
  refactoring (~35 lines net change).

## Commit

- `143dce5` — pull: Phase 14 (early) — bundle six paper primitives
  into PartiallySynchronousFairness.

## What's next

Continue Phases 10–13:

- **Phase 10**: prove `EventualRoundAcceptance` from
  `h_prim.networkDelivery`, `h_prim.actionScheduling`,
  `h_prim.acceptScheduling` + model.
- **Phase 11**: prove `EventualCausalAcceptance` from
  `h_prim.networkDelivery`, `h_prim.actionScheduling`,
  `h_prim.acceptScheduling`, `h_prim.pullRequestDelivery`,
  `h_prim.pullResponseScheduling` + model.
- **Phase 12**: replace the `Eventual*` hypotheses on T2/T4 with
  the proved versions from Phases 10/11. The `h_prim` hypothesis
  then carries everything T2/T4 need; no separate `Eventual*`
  hypotheses required.
- **Phase 13**: final docs sync (formalization.md,
  mechanization-findings.md F-1c update).
