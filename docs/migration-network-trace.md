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
- [x] `network_honest_validator_persistent_trace` (commit `1dd5432`)
- [x] `network_round_intermediate_value` (commit `b75c03a`)
- [x] `networkStep_emittedOperations_monotone` + `networkTryActFor_emittedOperations_monotone` (commit `6a2e482`)
- [x] `networkStep_preserves_none` (commit `5d747da`)
- [x] `networkStep_advance_inversion` + 3 projections (commit `7672509`)

### Phase 2 — networkStep advance inversion (DONE)

- [x] `networkStep_advance_inversion` (commit `7672509`)
- [x] `networkStep_advance_implies_hasProposedFor` / `_stored` / `_gate`

### Phase 3 — Block / Accept / Causal invariants for `networkTrace` — REVISED SCOPE

**Status of `AcceptInv` migration**: `AcceptInv.acceptedParents` is
**not preserved** by `networkStep` because the accept branch fires
on `canAcceptBlock` which includes the ImPoA path (paper §4.3 f+1
references). When ImPoA fires, `vid` accepts a block whose parents
are not necessarily directly accepted by `vid`. So `acceptedParents`
fails for `networkTrace`.

This is a *paper-faithful* finding: `AcceptInv.acceptedParents`
captures the strong invariant of the simpler `belugaTrace` model
(no ImPoA); under the ImPoA-aware `networkTrace`, only the weaker
invariant holds — vid has either accepted or has implicit
availability of every parent.

**Consequences for §5 conclusions**:
- T1 (block availability) needs only `acceptedBlockExists`, not
  `acceptedParents`. We extract this as a standalone invariant
  `network_acceptedBlockExists_trace` (a single conjunct of
  `AcceptInv` that does survive ImPoA).
- T2 (causal availability) **requires the full** `CausallyClosed`,
  which doesn't survive ImPoA. T2 under `networkTrace` is genuinely
  weaker than under `belugaTrace`: the paper §5 T2 prose proof
  invokes a liveness argument (the validator eventually pulls /
  accepts all causal ancestors), which is downstream of paper
  §4.3 ImPoA + the pull mechanism. Mechanizing this requires a
  separate liveness argument; not a structural inductive invariant.
  See [`docs/mechanization-findings.md` § F-1c](mechanization-findings.md)
  for the broader paper-implicit assumption issue.

So Phase 3 reduces to:

- [ ] `network_acceptedBlockExists_trace` (1 conjunct of full AcceptInv)

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

### Session 2026-04-27

**Phase 1 COMPLETE** (10 helpers, commits `d65b2a5` through `5d747da`):

- `deliverPending_preserves_base`
- `networkTryActFor_round_monotone`/`_at_most_one`
- `networkStep_round_monotone`/`_at_most_one`
- `network_round_monotone_trace`
- `network_honest_validator_persistent_trace`
- `network_round_intermediate_value`
- `networkTryActFor_emittedOperations_monotone` + `networkStep_emittedOperations_monotone`
- `networkStep_preserves_none`

All in `Beluga/Network/Fairness.lean`, no sorries.

**Phase 5 partial** (L1, L2 done; commit `0c97a86`): new file
`Beluga/Network/Theorems.lean` with:

- `network_lemma1_honest_round_entry` — direct from `schedulerFairness_holds`
- `network_lemma2_round_latency` — composes L1 + `network_round_intermediate_value`

**Phase 2 attempted but blocked**: `networkStep_advance_inversion`
(~150 lines mirror of `step_advance_inversion`) was attempted but
reverted due to several issues:

- The `set s_delivered := ...; unfold networkStep at h'` doesn't make
  `s_delivered` match the unfolded form's local `have` binding —
  the rewrites fail.
- Use the `split at h'` pattern (as in `networkStep_currentTime`)
  instead of `rcases h_fs : List.findSome? ...` to keep terms aligned.
- The conclusions need adjustment: accept-disabled becomes about
  `canAcceptBlock = false` (not the `parents.all hasAcceptedDigest`
  form); advance-gate becomes `allProposedFor ∨ timeoutFired`.

Next session: complete `networkStep_advance_inversion` using the
`split at h'` pattern. Once that lemma closes, the projection
lemmas (`networkStep_advance_implies_*`) follow directly.

After Phase 2: Phase 3 (block invariants) is the bulk of remaining
work — `BlockInv` / `AcceptInv` / `CausallyClosed` for `networkTrace`
require the `*_step` preservation proofs to be redone for
`networkStep`, which adds the ImPoA-accept and timeout-advance
branches to each preservation case-split.
