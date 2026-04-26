# Aristotle project tracker

The map from Aristotle project IDs to the files/theorems they're responsible
for. Updated whenever a submission is created or completes.

Status legend: 🟡 IN_PROGRESS · ✅ COMPLETE (integrated) · ⚠️ COMPLETE_WITH_ERRORS
· ❌ FAILED / OUT_OF_BUDGET · 🚫 CANCELED.

## Active

| Project ID | Round | Submitted | Status | Target file(s) | Theorem(s) | Result |
|---|---|---|---|---|---|---|
| `3f6cf619-5a7f-4142-9114-c46caafa025f` | 4-followup | 2026-04-26 ~02:30 SGT | 🟡 IN_PROGRESS | [`Beluga/Protocol.lean`](../BlockSynchroniser/Beluga/Protocol.lean) | `causal_history_of_find_none` (trace-level invariant; prompt suggests strengthening to `CausallyClosed` carrier + monotonicity lemmas) | pending |
| `e3bb7fb6-40cd-4cd9-8f22-c8f8e6c621fc` | theorems-mains | 2026-04-26 ~10:30 SGT | 🟡 IN_PROGRESS | [`Beluga/Theorems.lean`](../BlockSynchroniser/Beluga/Theorems.lean) | L1, L2, T1, T2, T3, T4 (under `SchedulerFairness`); helpers `step_preserves_validator_ids` + `step_round_monotone` are now sorry-free | pending |

**2 projects in flight in parallel.** Aristotle accepts concurrent
submissions; they will process as capacity allows.

Frozen files (do not edit until corresponding rounds complete):
- `Beluga/Protocol.lean` (round 4-followup)
- `Beluga/Theorems.lean` (theorems-mains round)

Freely-editable files: `Lib/`, all base modules
(`Block`/`Validator`/`Operations`/`System`/`State`/`Causal`/`Trace`/`Properties`),
`Validation.lean` (Aristotle round 1 already complete), `Mysticeti/Consensus.lean`,
all Beluga supporting modules (`State`/`Reputation`/`AdmissionControl`/`Pull`/`BlockExt`/`Examples`).

## Queued (planned for after round 2)

| Target file(s) | Theorem(s) | Notes |
|---|---|---|
| [`Beluga/Theorems.lean`](../BlockSynchroniser/Beluga/Theorems.lean) | `theorem3_round_progression`, `theorem4_round_termination` | Should follow once L1, L2 are stated cleanly with timing. |
| [`Beluga/Theorems.lean`](../BlockSynchroniser/Beluga/Theorems.lean) | `theorem1_block_availability`, `theorem2_causal_availability` | Depend on `step_refines_HonestStep` and pull mechanism. |
| [`Mysticeti/Safety.lean`](../BlockSynchroniser/Mysticeti/Safety.lean) | `lemma13_cert_persistence`, `lemma14_no_skip`, `lemma16_consistent_status`, `theorem7_consensus_safety` | After round 2 lands `quorumIntersection` and `lemma10`, these are pure quorum-intersection chains. |
| [`Mysticeti/Liveness.lean`](../BlockSynchroniser/Mysticeti/Liveness.lean) | L8, L9, L11, L12, T6 | Timing-flavored; biggest dependency tier. |
| [`Beluga/Theorems.lean`](../BlockSynchroniser/Beluga/Theorems.lean) | L1, L2 (timing) | Foundation for many liveness proofs. |
| [`Beluga/StepPreservation.lean`](../BlockSynchroniser/Beluga/StepPreservation.lean) | `tryActFor_preserves_reputation` | Round-3e left this as `sorry` due to a `▸` cast mismatch + heartbeat timeout in the doAccept branch. Followup: case-split by hand or hint Aristotle to use `convert`/`refine` instead of `▸`. |

## Completed

| Project ID | Submitted | Returned | Status | Target file(s) | Theorem(s) | Integration commit |
|---|---|---|---|---|---|---|
| `be7c0245-cdb9-4cce-9c4a-fffecfd1a69c` | 2026-04-25 21:25 SGT | 2026-04-25 ~22:50 SGT | ⚠️ COMPLETE_WITH_ERRORS (all 4 target sorries closed cleanly) | [`Validation.lean`](../BlockSynchroniser/Validation.lean) | `golden_roundProgression`, `golden_roundTermination`, `golden_blockAvailability`, `golden_causalAvailability` (+11 helper lemmas) | `009bb10` |
| `116385ce-5fc6-4f0c-8083-a2ed4c66d514` | 2026-04-25 23:14 SGT | 2026-04-26 ~00:24 SGT | ⚠️ COMPLETE_WITH_ERRORS (structural proof, 5 inline gaps; iterated as round 4 below) | [`Beluga/Protocol.lean`](../BlockSynchroniser/Beluga/Protocol.lean) | `step_refines_HonestStep` (+3 helpers) | `d96ce2e` |
| `47e91c18-161d-4b4c-a702-d30f18883282` | 2026-04-25 23:22 SGT | 2026-04-26 ~00:33 SGT | ⚠️ COMPLETE_WITH_ERRORS (L14 fully proved; L13/L16/T7 structural with bridge sorries) | [`Mysticeti/Safety.lean`](../BlockSynchroniser/Mysticeti/Safety.lean) | `lemma14_no_skip` (sorry-free); `lemma13_cert_persistence`, `lemma16_consistent_status`, `theorem7_consensus_safety` (structural) | (TBD) |
| `84e08b81-d35a-4ca9-80d7-a69a35192e58` | 2026-04-25 23:22 SGT | 2026-04-26 ~00:33 SGT | ⚠️ COMPLETE_WITH_ERRORS (5 main theorems sorry-free, delegating to 11 sorry'd helper lemmas) | [`Mysticeti/Liveness.lean`](../BlockSynchroniser/Mysticeti/Liveness.lean) | `lemma8_leader_referenced`, `lemma9_honest_certificate`, `lemma11_eventual_decision`, `lemma12_referenced_accepted`, `theorem6_consensus_liveness` (+1 sorry-free helper) | (TBD) |
| `91c97602-54da-4277-8bda-3864bfa6674a` | 2026-04-25 23:18 SGT | 2026-04-26 ~01:07 SGT | ⚠️ COMPLETE_WITH_ERRORS (L3, L4, L5 sorry-free; helper `tryActFor_preserves_reputation` left as sorry — `▸` + heartbeat issue, queued for round 3e-followup) | [`Beluga/PerformanceLemmas.lean`](../BlockSynchroniser/Beluga/PerformanceLemmas.lean), [`Beluga/StepPreservation.lean`](../BlockSynchroniser/Beluga/StepPreservation.lean) (new) | `lemma3_honest_not_blamed`, `lemma4_round_latency_delta`, `lemma5_round_latency_or_blamed` (+`LatencyTriangle` def, +6 helpers in StepPreservation) | (TBD) |
| `d724efd2-324b-48c2-bd1d-08e690d02eb1` | 2026-04-25 23:13 SGT | 2026-04-26 ~01:28 SGT | ⚠️ COMPLETE_WITH_ERRORS (claimed paper L1/L2 false; supplied weaker corrected versions). **Discarded the weakening, preserved as discovery (see [paper-feedback-l1-l2-fairness.md](paper-feedback-l1-l2-fairness.md))**; restated paper L1/L2 with new `SchedulerFairness` hypothesis instead. | [`Beluga/Theorems.lean`](../BlockSynchroniser/Beluga/Theorems.lean) | `lemma1_honest_round_entry`, `lemma2_round_latency` (timing) | (TBD) |
| `af54716b-b1b4-41d5-bbb7-d02d0e0dab2a` | 2026-04-25 23:21 SGT | — | 🚫 CANCELED (file was conflicting with r3a follow-up) | [`Beluga/Theorems.lean`](../BlockSynchroniser/Beluga/Theorems.lean) | `theorem3_round_progression`, `theorem4_round_termination` | — |
| `bb79d236-f91d-42e0-9315-f46d9a22f5b8` | 2026-04-26 01:11 SGT | 2026-04-26 ~01:33 SGT | ✅ COMPLETE (sorry-free; standard axioms only) | [`Beluga/StepPreservation.lean`](../BlockSynchroniser/Beluga/StepPreservation.lean) | `tryActFor_preserves_reputation` | (TBD) |
| `9d7e8e08-0f3f-4101-9b69-2a46a7f6a69a` | 2026-04-26 00:46 SGT | 2026-04-26 ~01:31 SGT | ✅ COMPLETE (3 bridge sorries closed; added 4 paper-faithful protocol-invariant hypotheses + new `Reaches.trans` lemma) | [`Mysticeti/Safety.lean`](../BlockSynchroniser/Mysticeti/Safety.lean) | `lemma13_cert_persistence`, `lemma16_consistent_status`, `theorem7_consensus_safety` | (TBD) |
| `a8889396-b34e-40f2-b10b-388f960c088e` | 2026-04-26 00:46 SGT | 2026-04-26 ~02:20 SGT | ⚠️ COMPLETE_WITH_ERRORS (`step_refines_HonestStep` proved sorry-free; one new sorry on trace-level invariant `causal_history_of_find_none`, deferred to a future trace-invariant module) | [`Beluga/Protocol.lean`](../BlockSynchroniser/Beluga/Protocol.lean) | `step_refines_HonestStep` (+7 helper lemmas) | (TBD) |
| `d32908b4-d387-4d77-ac37-87e03a6f6699` | 2026-04-26 00:46 SGT | 2026-04-26 ~05:30 SGT | ⚠️ COMPLETE_WITH_ERRORS (11 helpers got structured proofs composing other lemmas + paper §D.2 arguments; 14 inline sorries remain on protocol-invariant sub-steps — step semantics, BFT-bound, parent selection, ImPoA-availability, TransactionOrder axioms; 2 fully-proved auxiliaries `belugaTrace_blocks_monotone` + `mem_of_mem_eraseDups`) | [`Mysticeti/Liveness.lean`](../BlockSynchroniser/Mysticeti/Liveness.lean) | 11 helpers underlying lemma8/9/11/12/T6 (round 3d chain) | (TBD) |
| `9f17cf80-caba-4369-90b2-0a99a175e394` | 2026-04-26 03:00 SGT | 2026-04-26 ~07:30 SGT | ⚠️ COMPLETE_WITH_ERRORS (both target sorries closed cleanly via a compound `TraceInv` for the admission invariant + strong induction with `Quorum.quorumIntersection` for L13; one new hypothesis `h_honest_unique` added to L13; standard axioms only) | [`Beluga/AdmissionInvariant.lean`](../BlockSynchroniser/Beluga/AdmissionInvariant.lean) (new), [`Mysticeti/Safety.lean`](../BlockSynchroniser/Mysticeti/Safety.lean) | `belugaTrace_admissionWellFormed`, revised `lemma13_cert_persistence` | (TBD) |
| `58873be7-0f63-412c-8029-873bbd930abe` | 2026-04-26 01:50 SGT | (canceled 2026-04-26 ~09:05 SGT) | 🚫 CANCELED — stalled at 13% progress for >7h. Replaced by `b544affb-...` with a tighter 2-helper scope. | [`Beluga/Theorems.lean`](../BlockSynchroniser/Beluga/Theorems.lean) | (was) L1, L2, T1, T2, T3, T4 + 2 helpers under SchedulerFairness | — |
| `b544affb-b9a9-4f8c-965f-2a31051ef75f` | 2026-04-26 09:05 SGT | 2026-04-26 ~10:25 SGT | ✅ COMPLETE (clean — both target helpers proved sorry-free; new auxiliary `updateValidator_none` added; `set_option maxHeartbeats 800000 in` scoped per-lemma; standard axioms only) | [`Beluga/Theorems.lean`](../BlockSynchroniser/Beluga/Theorems.lean) | `step_preserves_validator_ids`, `step_round_monotone` | (TBD) |

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
