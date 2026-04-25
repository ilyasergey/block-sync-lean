# Aristotle project tracker

The map from Aristotle project IDs to the files/theorems they're responsible
for. Updated whenever a submission is created or completes.

Status legend: 🟡 IN_PROGRESS · ✅ COMPLETE (integrated) · ⚠️ COMPLETE_WITH_ERRORS
· ❌ FAILED / OUT_OF_BUDGET · 🚫 CANCELED.

## Active

| Project ID | Submitted | Status | Target file(s) | Theorem(s) | Result |
|---|---|---|---|---|---|
| `4cda6cb1-a5b1-4f2f-9616-204e6438f82d` | 2026-04-25 ~22:55 SGT | 🟡 IN_PROGRESS | [`Quorum.lean`](../BlockSynchroniser/Quorum.lean), [`Beluga/Patterns.lean`](../BlockSynchroniser/Beluga/Patterns.lean), [`Mysticeti/Safety.lean`](../BlockSynchroniser/Mysticeti/Safety.lean) | `quorumIntersection`, `certified_unique`, `lemma10_round_robin_pigeonhole` | pending |

Frozen files (do not edit until round completes): `Quorum.lean`,
`Beluga/Patterns.lean`, `Mysticeti/Safety.lean`.

## Queued (planned for after round 2)

| Target file(s) | Theorem(s) | Notes |
|---|---|---|
| [`Beluga/Theorems.lean`](../BlockSynchroniser/Beluga/Theorems.lean) | `theorem3_round_progression`, `theorem4_round_termination` | Should follow once L1, L2 are stated cleanly with timing. |
| [`Beluga/Theorems.lean`](../BlockSynchroniser/Beluga/Theorems.lean) | `theorem1_block_availability`, `theorem2_causal_availability` | Depend on `step_refines_HonestStep` and pull mechanism. |
| [`Mysticeti/Safety.lean`](../BlockSynchroniser/Mysticeti/Safety.lean) | `lemma13_cert_persistence`, `lemma14_no_skip`, `lemma16_consistent_status`, `theorem7_consensus_safety` | After round 2 lands `quorumIntersection` and `lemma10`, these are pure quorum-intersection chains. |
| [`Mysticeti/Liveness.lean`](../BlockSynchroniser/Mysticeti/Liveness.lean) | L8, L9, L11, L12, T6 | Timing-flavored; biggest dependency tier. |
| [`Beluga/Theorems.lean`](../BlockSynchroniser/Beluga/Theorems.lean) | L1, L2 (timing) | Foundation for many liveness proofs. |
| [`Beluga/PerformanceLemmas.lean`](../BlockSynchroniser/Beluga/PerformanceLemmas.lean) | L3, L4, L5 (deterministic) | Reputation + timing; substantive. |

## Completed

| Project ID | Submitted | Returned | Status | Target file(s) | Theorem(s) | Integration commit |
|---|---|---|---|---|---|---|
| `be7c0245-cdb9-4cce-9c4a-fffecfd1a69c` | 2026-04-25 21:25 SGT | 2026-04-25 ~22:50 SGT | ⚠️ COMPLETE_WITH_ERRORS (all 4 target sorries closed cleanly; status name appears unrelated to actual result) | [`Validation.lean`](../BlockSynchroniser/Validation.lean) | `golden_roundProgression`, `golden_roundTermination`, `golden_blockAvailability`, `golden_causalAvailability` (+11 helper lemmas) | `009bb10` |

Full attribution detail in [aristotle-attributions.md](aristotle-attributions.md).

## Conventions

- **One project per logical batch.** Don't bundle unrelated theorems.
- **Frozen files.** While a project is `IN_PROGRESS`, the listed target file(s)
  must not be edited locally. If urgent, run `aristotle cancel <id>` and
  update this tracker to 🚫.
- **Provenance.** Every Aristotle-filled proof carries
  `-- proof filled by Aristotle (project <id>)` above it; commit messages
  cite the project ID.
- **Update this file on every state change.** Submission → add to *Active*.
  Completion → move to *Completed* with the integration commit hash.

## Workflow reference

See [aristotle-workflow.md](aristotle-workflow.md) for the operational
recipe (submit → extract → diff → review → apply → verify → commit) and the
delegation policy (token-aware attempt budget, concurrency rule).
