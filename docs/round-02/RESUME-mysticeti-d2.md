# Resume notes — finishing Mysticeti §D.2 (zero sorries, zero axioms, no-stronger-than-paper)

## Goal

Discharge the 8 sorry conjuncts in
`MysticetiPostGSTLiveness` (Mysticeti/Liveness.lean) by deriving
each §D.2 result from `BelugaWithPullFairness` + paper-implicit
per-action liveness primitives (no §D.2-conclusion shortcuts in
the bundle).

## Architectural blocker

The current §D bundle and downstream lemmas (L8, L9, L11, L12, T6)
are stated against `belugaTrace` — the synchronous executable
trace — with `time : TimeMap` + `PartiallySynchronous` as the
post-GST contract. But the §5 results we'd compose them out of
(L1, T1–T4, plus `inPoolDelivery`/`acceptScheduling`) are stated
against `networkBelugaTraceWithPull` under `BelugaWithPullFairness`.
Without refactoring §D to the network-aware trace, no derivation
of the §D.2 lemmas from §5 results is possible.

## Refactor plan (not yet executed)

1. **Generalize `belugaTransactionOrder`** ([Beluga/Order.lean](../../BlockSynchroniser/Beluga/Order.lean)):
   take a `BelugaState` instead of computing `belugaTrace system k`
   internally. Adapt `accepted_implies_in_belugaTransactionOrder`
   accordingly.

2. **Replace `MysticetiPostGSTLiveness`'s parameters** from
   `(system, time : TimeMap)` to `(system, time : Nat → Nat)`.
   Replace `belugaTrace` references with `networkBelugaTraceWithPull
   system time`. Add the missing preconditions (e.g.,
   `honest_round_entry` needs "some honest at round `r` at step
   `k`" — currently absent; conjunct as stated is unprovable).

3. **Define `MysticetiBelugaSynchrony extends BelugaWithPullFairness`**
   adding two paper-implicit fields:
   - `proposeScheduling : ProposeSchedulingWithPull system time`
   - `storeScheduling : StoreSchedulingWithPull system time`

   Both already defined in
   [Network.lean](../../BlockSynchroniser/Beluga/Network.lean)
   (commit da0ba15, this branch).

4. **Refactor the constructor**
   `belugaTrace_satisfies_mysticeti_post_gst_liveness` →
   `mysticetiPostGSTLiveness_holds`: take `MysticetiBelugaSynchrony`,
   discharge each conjunct via derivation. Per-conjunct sketch:

   - `honest_round_entry` ← `lemma1_honest_round_entry` (1-line).
   - `leader_propose` ← L1 + `proposeScheduling` + tryActFor priority.
   - `honest_ref_leader` ← `leader_propose` + `networkDelivery` +
     L1 (for `r+1`) + admission-control parent inclusion.
   - `honest_certify_leader` ← apply `honest_ref_leader` to all
     `2f + 1` honest + `certificatePatternAtB` definition unfolding.
   - `three_consec_commit` ← `honest_certify_leader` (per round) +
     `lemma10_round_robin_pigeonhole` (already proved) + `directDecide`
     definition unfolding (`certificatePatternAtB` ⇒ ToCommit).
   - `backward_induction` ← backward induction over rounds using
     `lemma13_cert_persistence`, `lemma14_no_skip`,
     `lemma15_unique_cert` (all proved) + `indirectDecide` def.
   - `block_pull_liveness` ← `inPoolDelivery` +
     `acceptScheduling` + structural facts about the `f + 1`-references
     precondition (the referenced block is in the pool).
   - `honest_eventually_accepts` ← `inPoolDelivery` +
     `acceptScheduling` (existing `network_eventualCausalAcceptance`
     captures the same content).

5. **Refactor downstream lemmas** to take `MysticetiBelugaSynchrony`
   and conclude over `networkBelugaTraceWithPull`:
   - `honest_round_entry_within_3delta` (rename to `_within_4delta`,
     adjust bound).
   - `leader_block_disseminated_within_delta`.
   - `honest_references_leader_within_4delta` (rename to `_within_5delta`).
   - `honest_validators_certify_leader`.
   - `three_consecutive_honest_direct_commit`.
   - `backward_induction_decides_earlier_rounds`.
   - `eventual_decision_core`.
   - `lemma8_leader_referenced`.
   - `lemma9_honest_certificate`.
   - `lemma11_eventual_decision`.
   - `at_least_f_plus_one_honest_referencers`.
   - `honest_blocks_eventually_received`.
   - `lemma12_referenced_accepted`.
   - `committed_leader_has_2f_plus_1_refs`.
   - `honest_validator_eventually_accepts`.
   - `theorem6_consensus_liveness`.

6. **Update [Mysticeti/Safety.lean](../../BlockSynchroniser/Mysticeti/Safety.lean)** if any wrapper still uses
   `belugaTrace` and needs to follow the network-aware trace
   (mostly L13/L15 wrappers — these are safety, may not need
   refactor if they're only state-level).

7. **Build clean** — zero sorries, zero axioms.

## Bound widening (paper-side, none affected)

Documented in [round-02-findings.md](round-02-findings.md) and
[paper-additions-stage3.md](paper-additions-stage3.md):
no §D.2 paper statement contains a `cΔ` bound — they're all
"eventually"-quantified. Bound widening is bundle-internal:

- `honest_round_entry`: `3Δ` → `4Δ` (matches round-02 L1).
- `leader_propose`: `Δ` → unchanged (per-action scheduling).
- `honest_ref_leader`: `4Δ` → `6Δ` (`5Δ` for L1 + Δ for delivery + Δ for next-round entry).
- `honest_certify_leader`: `4Δ` → `6Δ`.

## Paper-faithful additions (stage-4 candidate)

Two paper-implicit primitives added to `BelugaPartialSynchrony`'s
extension `MysticetiBelugaSynchrony`:

- **Per-action `block_propose` scheduling** (paper §4.2 implicit,
  matches the paper's symmetric per-action treatment of the four
  actions; `acceptScheduling` is already in the bundle).
- **Per-action `block_store` scheduling** (paper §4.2 implicit,
  same justification).

Stage-4 should note these and include them as Items 5b, 5c of
the §5 partial-synchrony assumption, marked as additionally
needed by §D.2.

## What's done so far (commit da0ba15 on this branch)

- `ProposeSchedulingWithPull` and `StoreSchedulingWithPull`
  defined in [`Network.lean`](../../BlockSynchroniser/Beluga/Network.lean).
- Build clean.

## Next session entry point

Open [Mysticeti/Liveness.lean](../../BlockSynchroniser/Mysticeti/Liveness.lean)
and start at step (1) of the refactor plan above. The
`MysticetiBelugaSynchrony` definition can go directly above
the `MysticetiPostGSTLiveness` definition.
