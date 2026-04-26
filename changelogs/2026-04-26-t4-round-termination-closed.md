# 2026-04-26 — T4 (round_termination) closed; Beluga §5 bundle sorry-free

## What changed

Closed paper §5 **T4 (Round-Termination)** in `Beluga/Theorems.lean`,
discharging the last `sorry` in the post-GST liveness bundle.
`belugaTrace_satisfies_post_gst_liveness` is now fully sorry-free,
and `belugaTrace_isBlockSynchronizer` (the §5 corollary that Beluga
satisfies Definition 1) closes as a one-line conjunction.

### Refactor: `step_advance_inversion`

The previous helpers `step_advance_implies_hasProposedFor` and
`step_advance_implies_stored` were merged into a single
`step_advance_inversion` lemma that returns all four advance-step
facts as a tuple:

1. **propose-before-advance**: `hasProposedFor s vid bv.currentRound = true`
2. **accept-disabled**: `∀ B ∈ s.blocks, hasAcceptedDigest s vid B.d = true ∨ ∃ pd ∈ B.parents, hasAcceptedDigest s vid pd = false`
3. **store-disabled**: `∀ B ∈ s.blocks, hasAcceptedDigest s vid B.d = true → hasStoredDigest s vid B.d = true`
4. **allProposedFor**: `allProposedFor system s bv.currentRound = true`

The two prior helpers are now 1-line projections. New projection
helpers `step_advance_implies_acceptComplete` and
`step_advance_implies_allProposedFor` are also added. This avoids
duplicating the 140-line case-analysis on `tryActFor`'s four
branches that was previously copy-pasted across helpers.

### New trace invariants

- **`block_parents_in_pool`** (Theorems.lean): for every `B ∈
  (trace k).blocks` and every `pd ∈ B.parents`, there exists `B_p
  ∈ (trace k).blocks` with `B_p.d = pd ∧ B_p.r + 1 = B.r`. (For
  round-0 blocks, this implicitly forces `B.parents = []` since
  no block has round `-1`.) Self-inductive on `k`: `doPropose`
  constructs parents as digests of round-`(r-1)` blocks in
  `s.blocks`, and other actions preserve `s.blocks`. ~150 lines.

- **`belugaTrace_proposeOp_in_pool`** (AdmissionInvariant.lean,
  promoted from the private `TraceInv`'s second conjunct): every
  `block_propose vid B r` op in the trace's emittedOperations
  corresponds to `B ∈ blocks ∧ B.author = vid ∧ B.r = r`. Used by
  T4 to bridge the `allProposedFor` gate (a fact about ops) to
  the count of distinct round-`round` blocks in the pool.

### T4 proof structure

`round_termination_aux` proves `RoundTermination system
(belugaTrace system)` directly, taking `(hids, time, h_time,
h_fair, hHonest, h_sys_nodup)`:

1. Use `all_honest_eventually_at_round` (iterated
   `SchedulerFairness`) + `round_intermediate_value` +
   `find_advance_step` to find a step `k_a` at which vid is at
   round `round` and advances to `round + 1` at `k_a + 1`.
2. `step_advance_implies_allProposedFor` gives `allProposedFor
   system (trace k_a) round = true` — every registered validator
   proposed for `round`.
3. **Inductive sub-claim** `accepted_at_advance`: at `k_a`, vid has
   accepted every `B ∈ blocks` with `B.r ≤ round`. Strong
   induction on `B.r`:
   - Accept-disabled at `k_a` gives "accepted ∨ ∃ unaccepted
     parent" for every B in pool.
   - For an unaccepted parent `pd ∈ B.parents`,
     `block_parents_in_pool` produces a round-`(B.r - 1)` block
     `B_p` in pool with `B_p.d = pd`. By IH (since
     `B_p.r < B.r ≤ round`), vid accepted `B_p.d = pd`.
     Contradiction.
4. For each `(vid_a, _) ∈ system.validators`:
   - `vid_a` proposed for `round` (gate).
   - `belugaTrace_proposeOp_in_pool` gives `B ∈ blocks` with
     `B.author = vid_a ∧ B.r = round`.
   - By (3), vid accepted `B.d`.
   - `authorOfDigest ops round B.d = some vid_a` via `BlockInv`'s
     `canonical` (with `hids`) and `digest_injective`: any propose
     op with digest `B.d` and round `round` must be authored by
     `vid_a`.
5. Counting via the same `eraseDups.length ≥ toFinset.card` bound
   as T3: `system.validators.length ≥ 2f+1` (from `hHonest`
   honest count + the trivial bound `honest ≤ total`), so
   `acceptedAuthors.eraseDups.length ≥ 2f+1`.

### Now-public lemmas

`acceptInv_trace` (Protocol.lean), `doPropose_blocks`,
`doStore_blocks_eq`, `doAdvance_blocks_eq`, `doAccept_blocks_eq`
(Protocol.lean) — all promoted from `private` to be usable from
Theorems.lean. `belugaTrace_proposeOp_in_pool` newly added as a
public extraction from AdmissionInvariant's TraceInv.

## Build state

`lake build` clean. **Beluga/Theorems.lean: 0 sorries** (was 1).
Mysticeti/Liveness.lean: 1 sorry unchanged.

## What's next (per user follow-up plan)

1. Sweep paper consistency vs current Lean development; any new
   findings beyond what Stage 2 already records.
2. Refactor: fold `ValidIds`, `ValidatorsNodup`, `HonestBFTBound`
   into the `BlockSynchroniserSystem` structure (the user's
   suggestion — fits the existing pattern of `honestMajority`,
   `validatorIdsUnique`, `validatorCountCorrect` Prop fields).
3. Clean up non-essential proof comments in `Theorems.lean`.
4. Add paper pseudocode to `Protocol.lean`'s `tryActFor` doc and
   explain the mapping to executable definitions.
5. Update `mechanization-findings.md`, `paper-additions-stage2.md`.
6. Read paper §5 prose proofs and write English rewrites that
   match our Lean proof strategy (where they diverge), into Stage
   2 doc.
