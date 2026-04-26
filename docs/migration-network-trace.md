# Migration plan — §5 theorems against `networkTrace`

> **Goal.** All §5 paper theorems (L1, L2, T1, T2, T3, T4, bundle,
> isBlockSynchronizer) stated against `networkTrace` (or its base
> projection), with all proofs derived from
> `Network.schedulerFairness_holds` plus structural invariants of
> `networkTrace` itself. No `NetworkBelugaCoherence` axiom; no
> sorries.

## Why this is large work

The existing §5 proofs for `belugaTrace` rest on ~25 helpers
operating on `step` / `belugaTrace`. Migrating means:

- Creating `networkStep` / `networkTrace` versions of every helper.
- Each helper's proof is typically a structural induction over the
  trace, case-splitting on the protocol step's branches.
- `networkStep` has more branches than `step` (ImPoA accept path,
  timeout advance path), so case analyses gain extra subcases.

Realistic scope: 1500–3000 lines of new proofs across multiple
sessions. The existing `belugaTrace` proofs in `Beluga/Theorems.lean`
serve as templates.

## Phase plan (each phase ends with a clean build)

### Phase 1 — Foundational `networkStep` lemmas

Helpers that establish algebraic properties of `networkStep`'s
effect on `base`:

- [x] `deliverPending_preserves_base` — full base equality (commit `d65b2a5`)
- [x] `networkTryActFor_round_monotone` — round never decreases (commit `fea1f3b`)
- [x] `networkTryActFor_round_at_most_one` — round increases ≤ 1 (commit `fea1f3b`)
- [x] `networkStep_round_monotone` (commit `aa8bb53`)
- [x] `networkStep_round_at_most_one` (commit `be42b5a`)
- [x] `network_round_monotone_trace` — trace-level k₁ ≤ k₂ ⇒ round monotone (commit `5233197`)
- [ ] `networkStep_advance_inversion` — inverse: if round
      advanced, the advance branch fired
- [ ] `networkStep_advance_implies_*` — projections of inversion
      (`hasProposedFor`, `stored`, `acceptComplete`)
- [ ] `networkStep_advance_implies_advanceGate` — `allProposedFor ∨ timeoutFired`
- [ ] `networkStep_preserves_none` — absence is preserved
- [ ] `networkStep_emittedOperations_monotone`
- [ ] `network_honest_validator_persistent_trace`

### Phase 2 — Block / Accept / Causal invariants for `networkTrace`

The invariant chain in `Beluga/Protocol.lean`:

- [ ] `NetworkBlockInv` — analog of `BlockInv` on `NetworkState.base`
- [ ] `networkBlockInv_trace` — invariant holds at every step
- [ ] `NetworkAcceptInv` + `networkAcceptInv_trace`
- [ ] `NetworkCausallyClosed` + `networkCausallyClosed_trace`

### Phase 3 — Trace-level helpers

- [ ] `network_honest_validator_persistent_trace`
- [ ] `network_round_monotone_trace`
- [ ] `network_round_intermediate_value`
- [ ] `network_proposed_for_lt_currentRound`
- [ ] `network_find_advance_step`
- [ ] `network_all_honest_eventually_at_round`
- [ ] `network_block_parents_in_pool`
- [ ] `network_accepted_at_advance`

### Phase 4 — §5 main theorems on `networkTrace`

- [ ] `network_round_progression_aux`
- [ ] `network_round_termination_aux`
- [ ] `NetworkBelugaPostGSTLiveness` bundle
- [ ] `networkTrace_satisfies_post_gst_liveness`
- [ ] `network_lemma1_honest_round_entry`
- [ ] `network_lemma2_round_latency`
- [ ] `network_theorem1_block_availability`
- [ ] `network_theorem2_causal_availability`
- [ ] `network_theorem3_round_progression`
- [ ] `network_theorem4_round_termination`
- [ ] `networkTrace_isBlockSynchronizer`

### Phase 5 — Cleanup

- [ ] Delete obsolete `belugaTrace`-flavored §5 wrappers and bundle
- [ ] Delete `NetworkBelugaCoherence` axiom
- [ ] Delete `belugaTrace_schedulerFairness` (no longer the path)
- [ ] Update Mysticeti chain (Safety, SafetyInvariant, Liveness)
      to use the network versions if their consumers reference §5
- [ ] Update `formalization.md`, `mechanization-findings.md`,
      `network-derivation-status.md` to reflect the final state

## Notes

- Many `private` helpers in `Beluga/Theorems.lean` (e.g.,
  `step_advance_inversion`, `belugaTrace_validators_nodup`) are not
  visible from `Network/Fairness.lean`. We either inline copies
  or move them to a shared location during the migration.
- Pure function-level lemmas (`doAccept_round`, `doStore_round`,
  `doAdvance_round`, `updateValidator_getValidator_*`) are
  trace-independent and apply to both `belugaTrace` and `networkTrace`
  — they can be moved to `Beluga/Protocol.lean`.
- The proofs of `networkStep_advance_inversion` and
  `networkStep_advance_implies_*` will *not* fully mirror their
  `step` counterparts because the advance gate is now
  `allProposedFor ∨ timeoutFired` (not just `allProposedFor`).
  Downstream consumers that depended on `allProposedFor` firing must
  be re-examined — they may need to handle the timeout case
  separately.
- T2 (causal availability) only requires `networkCausallyClosed_trace`
  and is independent of fairness; it's the easiest theorem to migrate.

## Checkpointing

Commit per phase, with a concrete count of lemmas closed in the
message body. Do not advance to the next phase until the current
phase builds cleanly with zero sorries.

## Session log

### Session 2026-04-27 (start)

Phase 1: 4 of ~10 foundational lemmas closed (commits `d65b2a5`,
`fea1f3b`, `aa8bb53`, `be42b5a`):

- `deliverPending_preserves_base`
- `networkTryActFor_round_monotone`
- `networkTryActFor_round_at_most_one`
- `networkStep_round_monotone`
- `networkStep_round_at_most_one`

Each builds clean, zero sorries, in `Beluga/Network/Fairness.lean`.

Next session priorities:

1. Finish Phase 1 — the trace-level monotonicity lemma
   `network_round_monotone_trace` (induction over `Nat.le` with `bv₂`
   generalized inside) and `network_honest_validator_persistent_trace`
   (use `getValidator_init_some` from `Beluga/Theorems.lean` for the
   init step, and `networkStep_preserves_ids` for the inductive step).

2. Phase 2 — start the inversion family
   (`networkStep_advance_inversion`). This is the largest single
   lemma (~150 lines for the `step` version); follows the case-split
   pattern from `Beluga/Theorems.lean` lines 735–894 but adds the
   timeout case to the advance branch.

3. Decide whether to make selected `private` helpers in
   `Beluga/Theorems.lean` public so the migration file (when split
   off) can use them, or keep migrating in
   `Beluga/Network/Fairness.lean`.
