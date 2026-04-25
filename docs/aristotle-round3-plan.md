# Aristotle round 3 plan

Submission plan for round 3, post-round-2 integration. Each batch is a
separate Aristotle project. Targets within a batch are *file-disjoint* so
diffs don't conflict.

Ordering rationale: each batch targets a specific module set so that
- diffs are contained (single tarball touches few files),
- post-round-2 dependencies are respected (don't submit batches that
  depend on round-2 results before round 2 returns),
- failure of one batch doesn't poison others.

## Prerequisites — wait for round 2 to land

Round 2 targets `quorumIntersection`, `certified_unique`,
`lemma10_round_robin_pigeonhole`. Several round-3 targets transitively
depend on these (especially `certified_unique` for safety lemmas, and
`quorumIntersection` for several arguments). **Submit round 3 batches
only after round 2's results are integrated.**

## Batch 3a — Beluga timing lemmas (L1, L2)

Files: `BlockSynchroniser/Beluga/Theorems.lean` only.

Targets:
- `lemma1_honest_round_entry` — after GST, all honest validators reach
  same round within 3Δ.
- `lemma2_round_latency` — round-to-round latency ≤ 3Δ in the happy
  case.

These are timing arguments using `PartiallySynchronous` and the
`time : TimeMap` parameter. Both have detailed PROVIDED SOLUTIONs from
paper §5.

**Prompt template**:
```
Fill in only `lemma1_honest_round_entry` and `lemma2_round_latency`
in BlockSynchroniser/Beluga/Theorems.lean. Both have PROVIDED SOLUTION
docstrings drawn verbatim from the paper. They use the timing
infrastructure from BlockSynchroniser/Timing.lean (TimeMap, Monotone,
Unbounded, PartiallySynchronous). Leave all other sorries unchanged.
```

## Batch 3b — Beluga Definition-1 theorems (T1–T4)

Files: `BlockSynchroniser/Beluga/Theorems.lean` only.

Targets:
- `theorem3_round_progression` — Beluga ⊨ Round-Progression.
- `theorem4_round_termination` — Beluga ⊨ Round-Termination.
- `theorem1_block_availability` — Beluga ⊨ Block availability.
- `theorem2_causal_availability` — Beluga ⊨ Causal availability.

Each has paper sketches in PROVIDED SOLUTION. T3, T4 depend on the
trace structure of `belugaTrace`. T1, T2 depend on the pull mechanism
(ImPoA from `BlockSynchroniser/Beluga/Pull.lean`).

These will likely require Aristotle to use `step` semantics; may
require an auxiliary "step preserves invariants" lemma.

**Prompt template**:
```
Fill in only the four theorems theorem1_block_availability,
theorem2_causal_availability, theorem3_round_progression,
theorem4_round_termination in BlockSynchroniser/Beluga/Theorems.lean.
Each has a paper PROVIDED SOLUTION docstring. They are stated against
belugaTrace from BlockSynchroniser/Beluga/Protocol.lean (which iterates
the executable `step`). Leave all other sorries unchanged. Helper
lemmas about `step` may be added if needed.
```

## Batch 3c — Mysticeti safety (L13, L14, L16, T7)

Files: `BlockSynchroniser/Mysticeti/Safety.lean` only.

Targets (post-round-2 integration order; each builds on the previous):
- `lemma13_cert_persistence`
- `lemma14_no_skip`
- `lemma16_consistent_status`
- `theorem7_consensus_safety`

All should reduce to quorum-intersection chains plus the strengthened
`NoEquivocationInParents`. PROVIDED SOLUTIONs are in place.

`lemma15_unique_cert` is already proved (one-line specialization of
`certified_unique`).

**Prompt template**:
```
Fill in only lemma13_cert_persistence, lemma14_no_skip,
lemma16_consistent_status, and theorem7_consensus_safety in
BlockSynchroniser/Mysticeti/Safety.lean. Each has a paper PROVIDED
SOLUTION docstring. The proofs depend on Quorum.quorumIntersection
(round 2) and Beluga.certified_unique (round 2). The Mysticeti
namespace defines ConsensusView and TransactionOrder that L14, L16, T7
parameterize over. Leave all other sorries unchanged.
```

## Batch 3d — Mysticeti liveness (L8, L9, L11, L12, T6)

Files: `BlockSynchroniser/Mysticeti/Liveness.lean` only.

Targets:
- `lemma8_leader_referenced`
- `lemma9_honest_certificate`
- `lemma11_eventual_decision`
- `lemma12_referenced_accepted`
- `theorem6_consensus_liveness`

Timing-flavored. Use `PartiallySynchronous` from Timing.lean. Each has
paper sketches in PROVIDED SOLUTION.

**Prompt template**:
```
Fill in lemma8_leader_referenced, lemma9_honest_certificate,
lemma11_eventual_decision, lemma12_referenced_accepted, and
theorem6_consensus_liveness in BlockSynchroniser/Mysticeti/Liveness.lean.
Each has a paper PROVIDED SOLUTION docstring. They use the timing
infrastructure from BlockSynchroniser/Timing.lean and depend on the
Mysticeti consensus rules. Leave all other sorries unchanged.
```

## Batch 3e — Beluga performance lemmas (L3, L4, L5)

Files: `BlockSynchroniser/Beluga/PerformanceLemmas.lean` only.

Targets:
- `lemma3_honest_not_blamed`
- `lemma4_round_latency_delta`
- `lemma5_round_latency_or_blamed`

Reputation + timing arguments. Paper assumes "latency triangle"
(Assumption 1, Appendix C); statements may need that as an additional
hypothesis. Paper sketches in place.

**Prompt template**:
```
Fill in lemma3_honest_not_blamed, lemma4_round_latency_delta, and
lemma5_round_latency_or_blamed in
BlockSynchroniser/Beluga/PerformanceLemmas.lean. Each has a paper
PROVIDED SOLUTION docstring. They reason about the reputation
mechanism (Beluga/Reputation.lean) under partial synchrony
(Beluga/Protocol.lean + Timing.lean). Leave all other sorries
unchanged.
```

## Batch 3f — Beluga Protocol step refinement

Files: `BlockSynchroniser/Beluga/Protocol.lean` only.

Targets:
- `step_refines_HonestStep` — full case analysis on `tryActFor`'s 4
  branches × honest/Byzantine.

The witness extraction step (`Lib.findSome_witness`) is in place. The
remaining case analysis is mechanical but requires patient Lean tactic
work.

**Prompt template**:
```
Fill in step_refines_HonestStep in BlockSynchroniser/Beluga/Protocol.lean.
The PROVIDED SOLUTION docstring describes the proof structure: extract
(vid, bv) from findSome? via Lib.findSome_witness (already imported);
case-split on tryActFor's four branches (propose / accept / store /
advance); for each branch, case-split on isHonestValidator system vid
to choose between the corresponding HonestX disjunct or ByzantineStep
with the new operation as a singleton newOps list. Leave all other
sorries unchanged.
```

## Submission order recommendation

1. **Round 3a** (Beluga L1, L2) — independent of round 2 results. Submit early.
2. **Round 3b** (Beluga T1–T4) — depends on `step` semantics; submit
   after 3a.
3. **Round 3c** (Mysticeti safety) — depends on round-2's
   `quorumIntersection` + `certified_unique` being landed.
4. **Round 3d** (Mysticeti liveness) — depends on 3c.
5. **Round 3e** (Beluga performance) — independent of 3a–3d but uses
   timing.
6. **Round 3f** (step_refines) — independent of all others; can be
   submitted in parallel with 3a.

If queue allows parallelism, 3a + 3f can go in parallel. Otherwise
sequential.

## Dependencies summary

```
Round 2 (in flight):
  quorumIntersection, certified_unique, lemma10
                                |
                                v
        +-----------+-----------+-----------+
        |           |           |           |
       3a          3c          3e          3f
   (timing)    (safety)    (perf)      (step)
        |           |
        v           v
       3b          3d
    (T1–T4)    (liveness)
```

## Failure handling

If a batch returns `COMPLETE_WITH_ERRORS`:
- Check the output tarball anyway (round 1 had this status but proofs
  worked).
- If proofs work in `lake build`, integrate.
- If not, refine the prompt and resubmit; do NOT cancel.

If a batch returns `FAILED`:
- Cancel and inspect the failure mode.
- May need to add more helper lemmas (in `Lib/`) or tighten
  hypotheses.

Ongoing project state in [aristotle-projects.md](aristotle-projects.md).
Per-project attribution in [aristotle-attributions.md](aristotle-attributions.md).
