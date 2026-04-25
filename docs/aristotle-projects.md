# Aristotle project tracker

The map from Aristotle project IDs to the files/theorems they're responsible
for. Updated whenever a submission is created or completes.

Status legend: 🟡 IN_PROGRESS · ✅ COMPLETE (integrated) · ⚠️ COMPLETE_WITH_ERRORS
· ❌ FAILED / OUT_OF_BUDGET · 🚫 CANCELED.

## Active

(none currently in flight)

## Queued (planned next submissions)

| Target file(s) | Theorem(s) | Notes |
|---|---|---|
| [`Quorum.lean`](../BlockSynchroniser/Quorum.lean) | `quorumIntersection` | BFT pigeonhole / inclusion-exclusion. PROVIDED SOLUTION already in docstring. |
| [`Beluga/Patterns.lean`](../BlockSynchroniser/Beluga/Patterns.lean) | `certified_unique` | Depends on `quorumIntersection` (no hard dependency for delegation, but cleaner if `quorumIntersection` lands first). |
| [`Mysticeti/Safety.lean`](../BlockSynchroniser/Mysticeti/Safety.lean) | `lemma10_round_robin_pigeonhole` | Pure combinatorics. Needs Mathlib `Finset.sum_le_card_nsmul` / `Finset.exists_lt_of_sum_lt`. Refined statement (added `n = 3f+1` and `honest count = 2f+1` hypotheses). Refined sketch. |

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
