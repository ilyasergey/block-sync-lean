# 2026-04-26 — T3 (round_progression) closed + side-condition abbrevs

## What changed

Closed paper §5 **T3 (Round-Progression)** in
`Beluga/Theorems.lean` from first principles, eliminating one of
the three remaining `sorry`s in the post-GST liveness bundle.

Also introduced two `abbrev`s, `HonestBFTBound system` and
`ValidatorsNodup system`, to keep the bundle's public signatures
readable and centralize the paper-§2 side-condition justifications
in one place.

### T3 proof structure

`round_progression_aux` proves
`RoundProgression system (belugaTrace system)` directly, taking
only `(time, h_time, h_fair, hHonest, h_sys_nodup)`:

1. Pick a witness honest validator `vid_w` from the nonempty
   honest filter (`hHonest ≥ 2f+1`).
2. Get a post-GST step `k₀` (`h_time.2`).
3. Apply `all_honest_eventually_at_round` (iterated
   `SchedulerFairness`) to obtain a step `k` at which every
   honest validator is at round `≥ round + 1`.
4. For each honest `vid`: by
   `proposed_for_lt_currentRound` (the propose-before-advance
   trace invariant), `vid` has proposed for the target round,
   so it appears in `proposers_raw` (the propose-ops at step
   `k` filtered by round).
5. Counting: `honest_vids ⊆ proposers_raw` lifts to
   `honest_vids.toFinset ⊆ proposers_raw.toFinset`; the bound
   `proposers_raw.eraseDups.length ≥ proposers_raw.toFinset.card`
   (proven inline via reverse-list induction following
   `Validation.lean`'s pattern) closes the `≥ 2f+1` goal.

### Helpers added in this commit

- `find_of_mem_nodup_fst` — generic find?-of-mem under
  nodup-by-fst, used to pin down records in `system.validators`.
- `isHonestValidator_of_mem` — `(vid, true) ∈ system.validators`
  + nodup ⇒ `isHonestValidator system vid = true`. Bridges
  `==`/`decide (=)` form via existing `find_beq_eq_find`.

### Abbrevs (per user request)

```
abbrev HonestBFTBound (system : BlockSynchroniserSystem) : Prop :=
  (system.validators.filter (fun p => p.2 = true)).length ≥ 2 * system.f + 1

abbrev ValidatorsNodup (system : BlockSynchroniserSystem) : Prop :=
  (system.validators.map Prod.fst).Nodup
```

Hoisted near the top of `Theorems.lean` (above the foundation
helpers) under a "Side conditions threaded through the bundle"
section; the long paper-§2 justification comment that previously
sat inline at each callsite now lives next to the abbrev.

Replaced literal `(system.validators.filter (fun p => p.2 = true)).length ≥ 2 * system.f + 1`
and `(system.validators.map Prod.fst).Nodup` everywhere they
appeared in public signatures (bundle theorem, L1, L2, T1, T3,
T4 wrappers, `belugaTrace_isBlockSynchronizer` corollary) and
in private helpers (`belugaTrace_validators_nodup`,
`proposed_for_lt_currentRound`, `isHonestValidator_of_mem`,
`round_progression_aux`).

## Build state

`lake build` clean. Beluga/Theorems.lean: **2 sorries** (was 3) —
T1 and T4 conjuncts of the bundle still pending.
Mysticeti/Liveness.lean: 1 sorry unchanged.

## What's next

- T4 (round_termination): structurally similar to T3 but with
  accept-before-advance gate instead of propose-before-advance.
  Will need an `accepted_for_lt_currentRound` trace invariant
  paired with a `step_advance_implies_hasAccepted_2f1` lemma.
- T1 (block_availability): `Eventually` claim from
  `HasAccepted` to `HasStored`. Uses store-before-advance gate
  + iterated `SchedulerFairness`.
