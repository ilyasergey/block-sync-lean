# Resume notes — Mysticeti §D.2 (closed)

§D.2 is closed end-to-end: zero sorries, zero axioms in
[`Mysticeti/Liveness.lean`](../../BlockSynchroniser/Mysticeti/Liveness.lean).
All non-probabilistic theorems of paper Appendix D.2 derive from
[`MysticetiBelugaSynchrony`](../../BlockSynchroniser/Mysticeti/Liveness.lean#L54)
which extends `BelugaWithPullFairness` with seven paper-stated
primitives (none is itself a §D.2 conclusion).

This file historically held a per-conjunct discharge plan when
§D.2 still had pending stubs. Kept for archival reasons; the
discharge happened, see commit
[`a9a99cd`](../../) and
[`changelogs/2026-04-28-mysticeti-d2-closed.md`](../../changelogs/2026-04-28-mysticeti-d2-closed.md).

## Where things landed

| §D.2 theorem | Lean name | Status |
|---|---|---|
| L7 (leader referenced) | `honest_ref_leader` | ✅ |
| L8 (leader certified) | `honest_certify_leader` | ✅ |
| L9 corollary (3 consecutive direct-commits) | `three_consec_commit` | ✅ |
| L11 existential (eventual direct commit) | `lemma11_eventual_commit` | ✅ |
| L12 (referenced ⇒ accepted) | `lemma12_referenced_accepted` | ✅ |
| T6 (consensus liveness) | `theorem6_consensus_liveness` | ✅ |

L11 in its full universal form ("every undecided leader's
decision is eventually decided via the indirect rule") requires
chaining `Mysticeti/Consensus.lean :: indirectDecideStep`
recursively through subsequent committed leaders. That recursion
is not mechanized — replaced by the existential corollary, which
is what's load-bearing for T6. T6 closes via §5 in-pool delivery
+ §4.2 accept-action liveness directly and does not require the
backward indirect-rule chain.

## Bundle (`MysticetiBelugaSynchrony`)

```lean
structure MysticetiBelugaSynchrony (system) (time) : Prop
    extends Beluga.Network.BelugaWithPullFairness system time where
  proposeScheduling      : ProposeSchedulingWithPull system time   -- §4.2
  storeScheduling        : StoreSchedulingWithPull   system time   -- §4.2
  leader_inclusion       : ...                                       -- §D.1.2
  cert_pattern_at_r2     : ...                                       -- §D.1.1
  block_unique_by_digest : ...                                       -- §2.1 + §D.3 (iv)
  parent_blocks_in_pool  : ...                                       -- §2.1 + §4.2
  honest_block_uniqueness: ...                                       -- §3 + §D.3 (i)
```

All seven added fields are paper-stated rules anchored outside
§D.2. None is itself a §D.2 conclusion. Paper-side amendments are
documented in [`paper-additions-stage4.md`](paper-additions-stage4.md):
items 5b/5c (propose/store-action liveness) extend the §5
partial-synchrony assumption.

## Build state

`lake build`: clean (6252 jobs). Zero `sorry` and zero `axiom`
declarations across `BlockSynchroniser/`.
