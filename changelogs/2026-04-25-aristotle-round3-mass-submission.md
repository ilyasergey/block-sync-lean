# 2026-04-25 — Aristotle round 3 mass submission

User said "budget is not a concern" → submitted six round-3 batches in
parallel with the still-IN_PROGRESS round 2. **Seven Aristotle projects
running concurrently.**

## Submissions

| Project | Round | Target file | Theorems |
|---|---|---|---|
| `4cda6cb1-…` | 2 | Quorum.lean, Beluga/Patterns.lean, Mysticeti/Safety.lean | quorumIntersection, certified_unique, lemma10 |
| `d724efd2-…` | 3a | Beluga/Theorems.lean | L1, L2 (timing) |
| `af54716b-…` | 3b | Beluga/Theorems.lean | T3, T4 (round-progression, round-termination) |
| `47e91c18-…` | 3c | Mysticeti/Safety.lean | L13, L14, L16, T7 |
| `84e08b81-…` | 3d | Mysticeti/Liveness.lean | L8, L9, L11, L12, T6 |
| `91c97602-…` | 3e | Beluga/PerformanceLemmas.lean | L3, L4, L5 |
| `116385ce-…` | 3f | Beluga/Protocol.lean | step_refines_HonestStep |

## Discovery: Aristotle accepts concurrent submissions

Each project is independent on Aristotle's side — no queue
serialization observed. All seven moved to IN_PROGRESS within seconds
of submission. Wall-clock improvement over sequential submission
should be substantial.

## Cross-round dependency strategy

Some round 3 batches transitively depend on round 2's results
(e.g., `lemma13_cert_persistence` uses `quorumIntersection`).
Strategy: submit anyway with `quorumIntersection` invoked in the
proof body even though it's still `sorry`. Once round 2 lands and
`quorumIntersection` is proved, the transitive dependency
automatically resolves. The intermediate state has Aristotle's proofs
"compiled modulo round 2's target sorries."

This is the equivalent of `sorry`-bound modular development — the
proof structure exists, the foundation lemma is in flight.

## Frozen-files snapshot

| File | Frozen by |
|---|---|
| `Quorum.lean` | round 2 |
| `Beluga/Patterns.lean` | round 2 |
| `Mysticeti/Safety.lean` | round 2 + round 3c |
| `Beluga/Theorems.lean` | rounds 3a + 3b |
| `Beluga/PerformanceLemmas.lean` | round 3e |
| `Beluga/Protocol.lean` | round 3f |
| `Mysticeti/Liveness.lean` | round 3d |

Free for hand-work: `Lib/`, all base modules,
`Mysticeti/Consensus.lean`, all Beluga supporting modules
(`State`/`Reputation`/`AdmissionControl`/`Pull`/`BlockExt`/`Examples`),
`Validation.lean` (already Aristotle-filled, not frozen).

## What we did with the freeze window

- Created `Lib/Basic.lean` with `findSome_witness` (extracts a
  `findSome?` witness; useful for `step_refines_HonestStep`).
- Drafted [`docs/final-report-outline.md`](../docs/final-report-outline.md)
  for the eventual write-up.
- Drafted [`docs/aristotle-round3-plan.md`](../docs/aristotle-round3-plan.md)
  laying out the six-batch structure and prompts.
- Hand-attempted `step_refines_HonestStep` some-case (witness
  extraction works; full case analysis hit Lean tactic friction with
  match-result reduction; reverted).
- Strengthened Mysticeti placeholder conclusions
  (L14/L16/T7 with `ConsensusView`, T6 with `TransactionOrder`).

## Build state at submission time

`lake build` clean — 6242 jobs, 22 sorries (all queued for round 2 or
round 3 except 5 in `Mysticeti/Liveness.lean` and 1 in
`step_refines_HonestStep`).

## Next milestones

1. **Round 2 returns** (estimated based on round 1: ~1.5 hours
   from submission, so any time now). Integrate; unfreezes Quorum,
   Patterns, Safety files.
2. **Rounds 3a–3f return** (uncertain order; can be integrated
   independently as each returns).
3. **Each integration** = extract → diff → review → apply → verify
   → commit with provenance markers + attribution doc update.

If a round returns `COMPLETE_WITH_ERRORS` (as round 1 did), check
the proofs anyway — they often work despite the status.

If a round returns `FAILED`, inspect, possibly add helper lemmas to
`Lib/`, and resubmit with refined prompt.
