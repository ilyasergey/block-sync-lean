# 2026-04-25 — Aristotle round 1 integration + round 2 submission

Two milestones in this stage:

1. **Aristotle round 1 (`be7c0245`) returned and integrated.** All four
   `golden_*` theorems closed. First validation-level proofs landed.
2. **Aristotle round 2 (`4cda6cb1`) submitted** with three targets and a
   *narrow-scope prompt*.

## Aristotle round 1 integration

### What came back

Project `be7c0245-cdb9-4cce-9c4a-fffecfd1a69c`, status
`COMPLETE_WITH_ERRORS` (despite which all four sorries were closed
correctly — the status name appears unrelated to the proof outcome).
Output tarball `/tmp/aristotle-validation-20260425-212515.tar.gz`,
extracted to `/tmp/aristotle-out-validation/`.

Aristotle proved (per its `ARISTOTLE_SUMMARY.md`):

- `golden_roundProgression`, `golden_roundTermination`,
  `golden_blockAvailability`, `golden_causalAvailability`.
- 11 supporting helper lemmas (`gRoundOps_length`,
  `gOpsThrough_length`, `gOpsThrough_succ`, `gOpsThrough_take_full`,
  `goldenTrace_ops_at_full_round`, `gRoundOps_propose_mem`,
  `gRoundOps_accept_mem`, `gRoundOps_store_mem`,
  `gRoundOps_mem_gOpsThrough`, `propose_mem_gOpsThrough`,
  `accept_mem_gOpsThrough`, `store_mem_gOpsThrough`,
  `isHonest_goldenSystem_iff`).

All proofs use only standard axioms. Headline corollary
`goldenTrace_isBlockSynchronizer` no longer transitively depends on
any sorry.

### Integration steps taken

1. **Diff-and-pick**: only copied `BlockSynchroniser/Validation.lean`
   from the Aristotle tarball — other diffs were against my older
   pre-Phase-4 baseline (Aristotle's tarball reflects project state at
   submission time, not at integration).
2. **Build hiccup**: Aristotle added `import Mathlib` (kitchen-sink
   import). With this, the Lean library builds (16,000+ jobs!) but the
   *executable* fails to link — `clang` exits 255 because the link
   command exceeds OS arg-limit.
3. **Fix**: narrowed to `import Mathlib.Tactic` plus a few
   `Mathlib.Data.List.*` imports. Aristotle's proofs work unchanged.
   Build drops to 6,240 jobs, executable links cleanly.
4. **Provenance markers**: added `-- proof: aristotle (project
   be7c0245)` immediately above each Aristotle-proved declaration (4
   theorems + 11 helper lemmas section header).
5. **Attribution doc**: created
   [`docs/aristotle-attributions.md`](../docs/aristotle-attributions.md)
   as the source of truth for the final report's attribution
   section.

### Discovery: the `COMPLETE_WITH_ERRORS` quirk

Aristotle's status was `COMPLETE_WITH_ERRORS` despite all four target
sorries being filled correctly (verified by `lake build`). Possibly a
transient internal verifier issue on Aristotle's side. Worth
remembering: don't infer "proof failed" from that status; check the
output tarball and the `lake build` outcome.

## Aristotle round 2 submission

Project `4cda6cb1-a5b1-4f2f-9616-204e6438f82d`, IN_PROGRESS.

### Targets

Three independent tactical-wall items, all with `PROVIDED SOLUTION`
sketches in their docstrings:

- `quorumIntersection` (in `Quorum.lean`) — Mathlib `Finset.card_inter_*`.
- `certified_unique` (in `Beluga/Patterns.lean`) — uses
  `quorumIntersection` + cross-block `NoEquivocationInParents`.
- `lemma10_round_robin_pigeonhole` (in `Mysticeti/Safety.lean`) —
  pigeonhole over the round-robin schedule.

### Narrow-scope prompt technique

The submission used a **targeted prompt** explicitly naming the three
theorems and asking Aristotle to "leave all other sorries unchanged."

Originally the workflow doc described an `admit`-based scope-narrowing
trick — but in Lean 4 `admit` is a synonym for `sorry`, so Aristotle
sees them identically. Corrected the doc and used the targeted-prompt
approach instead.

If round 2 returns with only the three targeted sorries filled, this
confirms Aristotle respects targeted prompts and we have a reliable
narrowing mechanism for future rounds.

### Frozen files (per concurrency rule)

While round 2 is in flight, do not edit:
- `BlockSynchroniser/Quorum.lean`
- `BlockSynchroniser/Beluga/Patterns.lean`
- `BlockSynchroniser/Mysticeti/Safety.lean`

Other files (`Beluga/Protocol.lean`, `Mysticeti/Liveness.lean`, etc.)
remain free for parallel work.

## Mysticeti placeholder strengthening (`6c75b1a`)

In parallel, strengthened the `True`-conclusion placeholders in
Mysticeti theorems:

- New abstractions in `Mysticeti/Consensus.lean`: `ConsensusView`,
  `TransactionOrder`, plus `Consistent` predicates.
- `lemma13_cert_persistence` now states `∃ C, isCertificateFor B C ∧
  Reaches state B' C` (replaces `True`).
- `lemma14_no_skip` parameterized by view; concludes
  `∀ honest, view vid B.d ≠ ToSkip`.
- `lemma16_consistent_status` concludes `view.Consistent system`.
- `theorem7_consensus_safety` concludes `order.Consistent system`.
- `theorem6_consensus_liveness` concludes "every transaction in a
  post-GST honestly-accepted block ends up in every honest validator's
  order."

These conclusions are now meaningful (no longer trivially true), but
proofs all remain `sorry` — they're substantive and depend on
round-2 + further structural work.

## Build state

`lake build` clean (6,240 jobs). 22 sorries:

| File | Sorries |
|---|---|
| `Quorum.lean` | 1 (in flight) |
| `Beluga/Patterns.lean` | 1 (in flight) |
| `Beluga/Protocol.lean` | 1 (`step_refines_HonestStep` some case) |
| `Beluga/Theorems.lean` | 6 (L1, L2, T1–T4) |
| `Beluga/PerformanceLemmas.lean` | 3 (L3, L4, L5) |
| `Mysticeti/Safety.lean` | 5 (L10 in flight; L13, L14, L16, T7) |
| `Mysticeti/Liveness.lean` | 5 (L8, L9, L11, L12, T6) |

Net: 4 sorries closed by Aristotle round 1. 25 → 22.

## Next stage

While round 2 processes:

- Hand-attempt `step_refines_HonestStep` some case (no Mathlib needed).
- Continue documentation.
- When round 2 returns, integrate via the operational recipe.
