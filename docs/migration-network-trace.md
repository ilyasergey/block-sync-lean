# Migration plan — §5 theorems against `networkTrace` — COMPLETE

> **Goal.** All §5 paper theorems (L1, L2, T1, T2, T3, T4, bundle,
> isBlockSynchronizer) stated against `networkTrace` (or its base
> projection), with all proofs derived from
> `Network.schedulerFairness_holds` plus structural invariants of
> `networkTrace`. No `NetworkBelugaCoherence` axiom; no sorries
> in `Beluga/`.
>
> **Status: complete.** All six phases delivered. The new canonical
> §5 derivations live in
> [`BlockSynchroniser/Beluga/Network/Theorems.lean`](../BlockSynchroniser/Beluga/Network/Theorems.lean).

## Final state

- `Beluga/Network/Theorems.lean`: 9 §5 entry points
  (`network_lemma1_honest_round_entry`, `network_lemma2_round_latency`,
   `network_theorem1_block_availability`,
   `network_theorem2_causal_availability`,
   `network_theorem3_round_progression`,
   `network_theorem4_round_termination`,
   `networkTrace_isBlockSynchronizer`, plus the `networkBelugaTrace`
   projection and two paper-implicit liveness axioms).
- `Beluga/Network/Fairness.lean`: 18 helper theorems on
  `networkStep` and `networkTrace` (round monotonicity, advance
  inversion, persistence, intermediate value, find-advance-step,
  all-honest-eventually-at-round, proposed-for-monotone, etc.).
- `Beluga/Theorems.lean`: trimmed to 1416 lines (was 2075). Helpers
  retained; §5 wrappers + bundle + `belugaTrace_isBlockSynchronizer`
  deleted.
- `Beluga/Network/Fairness.lean`: trimmed by ~170 lines.
  `NetworkBelugaCoherence`, `SchedulerFairness_belugaTrace`, and
  `belugaTrace_schedulerFairness` deleted (no longer needed once
  the §5 conclusions are about `networkTrace.base`).
- Build: clean, zero sorries in `Beluga/`.

## Paper-faithfulness summary

The §5 conclusions are now stated against the `networkTrace`
projection. The proofs route through:

- **`schedulerFairness_holds`** (proved theorem, Phase 5/6 of the
  Phase E network model) for L1/L2/T3 — the round-progression
  argument is fully derived from the network-trace primitives
  (NetworkDelivery, ActionScheduling, BoundedRoundSpread).
- **Structural invariants** for T1 — `network_acceptedBlockExists_trace`
  (a single conjunct of the `AcceptInv` chain that survives ImPoA),
  combined with `networkStep_advance_implies_stored` (Phase 2's
  inversion projection) and emittedOperations monotonicity.
- **Explicit liveness hypotheses** for T2 and T4 —
  `EventualCausalAcceptance` and `EventualRoundAcceptance` are
  Prop-level parameters capturing the paper-implicit pull-mechanism
  liveness claim that's not derivable from the structural model
  alone (paper §4.3 ImPoA + pull). These are the "honest, named
  axioms" surfacing the paper's hand-wave; see F-1c in
  `mechanization-findings.md`.

## Known limitations (paper-side)

Two paper-faithfulness gaps remain, both surfaced as named typed
hypotheses rather than buried in the proof:

1. **`EventualCausalAcceptance`** (T2): under ImPoA's f+1
   references rule, a validator can accept a block without
   directly accepting its parents. The paper's §5 T2 prose proof
   invokes the §4.3 pull mechanism to argue eventual acceptance.
   Mechanizing this requires modeling pull explicitly; we surface
   it as a typed Prop hypothesis.

2. **`EventualRoundAcceptance`** (T4): under the `T_rd = 4Δ`
   timeout (paper §4.2), a validator may advance its round
   without first accepting 2f+1 round-`r` blocks; the 2f+1
   acceptances arrive later via pull. Same structural reason
   as (1); same resolution.

These are equivalent to F-1c (`NetworkBelugaCoherence` was the
analogous axiom for the round-progression slice) in spirit: the
paper's two informal abstractions (network model vs. simpler
§5 prose model) are silently equated, and where they diverge,
mechanization needs explicit liveness assumptions.

## Phase-by-phase commit log

### Phase 1 — Foundational `networkStep` lemmas (10 helpers)

- `deliverPending_preserves_base` (commit `d65b2a5`)
- `networkTryActFor_round_monotone` + `_at_most_one` (commit `fea1f3b`)
- `networkStep_round_monotone` (commit `aa8bb53`)
- `networkStep_round_at_most_one` (commit `be42b5a`)
- `network_round_monotone_trace` (commit `5233197`)
- `network_honest_validator_persistent_trace` (commit `1dd5432`)
- `network_round_intermediate_value` (commit `b75c03a`)
- `networkStep_emittedOperations_monotone` (commit `6a2e482`)
- `networkStep_preserves_none` (commit `5d747da`)

### Phase 2 — Step inversion (188-line theorem + 3 projections)

- `networkStep_advance_inversion` + `*_implies_hasProposedFor` /
  `_stored` / `_gate` (commit `7672509`)
- Helper `doAccept_round'` / `doStore_round'` (commit `b767306`)

### Phase 3 — Minimal AcceptInv extract

- `network_acceptedBlockExists_trace` (commit `0feb0a3`)

### Phase 4 — Trace-level helpers (4 more)

- `network_find_advance_step` (commit `45af3da`)
- `network_hasProposedFor_monotone` +
  `network_proposed_for_lt_currentRound` (commit `68efb5a`)
- `network_all_honest_eventually_at_round` (commit `4d33235`)

### Phase 5 — §5 main theorems on `networkTrace`

- L1, L2 (commit `0c97a86`)
- T1 (commit `345de95`)
- T3 (commit `5bcbfcc`)
- T2, T4, isBlockSynchronizer (commit `bd67b42`)

### Phase 6 — Cleanup

- Deleted `belugaTrace` §5 wrappers + `NetworkBelugaCoherence`
  axiom + `belugaTrace_schedulerFairness` derived corollary
  (commit `27d0fe5`, removes ~830 lines).
