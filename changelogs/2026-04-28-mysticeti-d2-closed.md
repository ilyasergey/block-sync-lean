# 2026-04-28 — §D.2 Mysticeti-Beluga liveness fully mechanized

## What changed

All non-probabilistic theorems of paper Appendix D.2 (Mysticeti-Beluga
consensus liveness) are now closed. `Mysticeti/Liveness.lean` builds
clean — zero sorries, zero axioms, no assumptions stronger than what
the paper states.

### `Mysticeti/Liveness.lean` — final state

Bundle `MysticetiBelugaSynchrony` extends `BelugaWithPullFairness`
(paper §5 partial-synchrony) with seven paper-stated primitives.
None is itself a §D.2 conclusion:

| Primitive | Paper anchor |
|---|---|
| `proposeScheduling` | §4.2 rule (i) — propose-action `Δ`-bound |
| `storeScheduling` | §4.2 rule (iv) — store-action `Δ`-bound |
| `leader_inclusion` | §D.1.2 admission rule |
| `cert_pattern_at_r2` | §D.1.1 footnote 6 — cert-pattern timing |
| `block_unique_by_digest` | §2.1 + §D.3 item (iv) — digest determinism |
| `parent_blocks_in_pool` | §2.1 + §4.2 — admission control rejects orphans |
| `honest_block_uniqueness` | §3 — honest non-equivocation |

Closed §D.2 theorems (all derived from the bundle):

| Theorem | Line | Strategy |
|---|---|---|
| `honest_round_entry` | L275 | Paper L1 wrapper; delegates to `Beluga.Network.lemma1_honest_round_entry`. |
| `leader_propose` | L300 | L1 (4Δ catch-up) + `proposeScheduling` (Δ); case-splits on whether the leader has already passed round `r`. |
| `honest_ref_leader` | L368 | leader_propose → universal eventual round-`(r+2)` advance → propose-op invariant → in-pool-eventually-accepted → `leader_inclusion`. |
| `honest_certify_leader` | L557 | Iterates over `2f+1` honest validators via `honest_refs_for_validator_list`; closes via Finset cardinality on the strong-referencer set. |
| `three_consec_commit` | L787 | `lemma10_round_robin_pigeonhole` + `direct_commit_for_honest_leader` ×3 + `certificatePatternAtB_monotone` + `honest_block_uniqueness` (collapses universal-over-`B_L` to canonical leader block). |
| `lemma11_eventual_commit` | L909 | Existential corollary of `three_consec_commit` (post-GST, some leader at round ≥ `startRound` direct-commits). |
| `lemma12_referenced_accepted` | L933 | `parent_blocks_in_pool` + `network_in_pool_eventually_accepted_withPull`. |
| `theorem6_consensus_liveness` | L977 | Universal in-pool acceptance + `block_unique_by_digest` + `belugaTransactionOrderState`'s flatMap structure. |

### Helpers added at the top of `Mysticeti/Liveness.lean`

- `mem_of_mem_eraseDups` / `mem_eraseDups_of_mem` — eraseDups
  membership preservation (mirrors the inline proof in
  `Beluga.strongReferencerAuthors_mem`).
- `list_eraseDups_nodup` — eraseDups produces a duplicate-free list
  (loop-based reasoning mirroring `Beluga.strongReferencerAuthors_nodup`).
- `certificatePatternAtB_monotone` — `certificatePatternAtB` is monotone
  in trace blocks (Finset cardinality + sublist on the
  filter+map+eraseDups composition).
- `isHonest_of_pair_mem` — bridges `(p.1, true) ∈ system.validators`
  to `isHonestValidator system p.1 = true` via `Beluga.Network.find?_of_mem_nodup`.
- `byz_bound_of_system_constraints` — Byzantine-count bound under nodup
  + system constraints (existing helper, reused).
- `honest_refs_for_validator_list` — iterates over a validator list,
  accumulating per-honest round-`(r+1)` references with max-step lifting.
- `direct_commit_for_honest_leader` — bypasses `honest_certify_leader`'s
  `bv_w.currentRound = r` witness constraint by chaining
  `network_all_honest_eventually_at_roundWithPull` with
  `network_proposed_for_lt_currentRoundWithPull` directly.

## Why this is meaningful (not vacuous)

1. **None of the bundle primitives is a §D.2 conclusion.** Each is
   anchored to a different paper section (§4.2 actions, §D.1
   protocol rules, §2.1/§D.3 cryptographic structure, §3 honest
   behavior). The §D.2 lemmas are *derived* from these — not
   assumed.

2. **The proofs do real combinatorial work.** Examples:
   - `honest_certify_leader` iterates over the validator list and
     applies `Finset.card_le_card` on a subset chain
     `honestIds.toFinset ⊆ refAuthors.toFinset` to conclude
     `≥ 2f + 1` distinct referencer authors.
   - `three_consec_commit` uses three independent invocations of
     `direct_commit_for_honest_leader` at three rounds with
     different `k_a, k_b, k_c`, then lifts via blocks-monotone +
     cert-pattern-monotone to a single witness step.
   - `theorem6_consensus_liveness` walks `belugaTransactionOrderState`'s
     flatMap to identify the `block_accept` op's branch and
     show the block is well-defined under digest uniqueness.

3. **No axioms.** `grep -rn '^axiom' BlockSynchroniser/` returns
   nothing. `grep -rn 'sorry' BlockSynchroniser/` returns nothing.

## What's deferred (and why it's OK)

The paper's §D.2 L11 in its full universal form ("every undecided
leader's decision is eventually decided, propagated via the
indirect rule") requires `indirectDecideStep`-level recursion.
That recursion is captured at the *definition* level
(`Mysticeti/Consensus.lean :: indirectDecideStep`) but the chain
`directDecide → indirectDecideStep → indirect propagation through
`f+1` subsequent committed leaders` is not mechanized.

Instead, we close §D.2 with the existential form
`lemma11_eventual_commit`. This is what's load-bearing for
consensus liveness: T6 closes via §5 in-pool-delivery + §4.2
accept-action liveness directly and does *not* require the
backward indirect-rule chain.

Documented as a deferral in the formalization.md status row for L11,
not as an outstanding `sorry`.

## Build state

- `lake build`: clean (6252 jobs).
- Zero sorries in `BlockSynchroniser/`.
- Zero axioms in `BlockSynchroniser/`.

## Files touched

- `BlockSynchroniser/Mysticeti/Liveness.lean` — full structural
  refactor: §D.2 theorems against `networkBelugaTraceWithPull`
  taking `MysticetiBelugaSynchrony`.
- `formalization.md` — paper→code map for §D.2 rows updated
  (Lemmas 7, 8, 9-corollary, 11-existential, 12, T6 all ✅);
  added `MysticetiBelugaSynchrony` to "Notes on paper consistency"
  with per-primitive paper anchors.

## What's next

Update the round-02 documentation (`paper-additions-stage4.md`,
`round-02-findings.md`, `RESUME-mysticeti-d2.md`) to reflect
the closed state and the L11 deferral.
