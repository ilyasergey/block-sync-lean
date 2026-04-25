# 2026-04-26 — multi-round integration session and paper-side findings

A long session that integrated four Aristotle rounds, identified
two paper-level concerns (F-1, F-7), surfaced three smaller ones
(F-3, F-5, F-8), and reorganised the docs accordingly. This entry
summarises the session at a coarse grain — per-round attribution
detail lives in [`docs/aristotle-attributions.md`](../docs/aristotle-attributions.md).

## Aristotle rounds integrated

| Project | Round | Targets | Outcome |
|---|---|---|---|
| `91c97602` | 3e | `Beluga/PerformanceLemmas.lean` (L3, L4, L5) | L3, L4, L5 sorry-free under `LatencyTriangle`; new helper module `Beluga/StepPreservation.lean` (5 sorry-free + 1 sorry'd helper) |
| `bb79d236` | 3e-followup | `Beluga/StepPreservation.lean` (`tryActFor_preserves_reputation`) | Closed (clean COMPLETE) |
| `9d7e8e08` | 6 | `Mysticeti/Safety.lean` (L13, L16, T7 bridge sorries) | All three bridges closed via 4 new paper-faithful protocol-invariant hypotheses + new `Reaches.trans` helper |
| `4cda6cb1` | 2 | `Quorum.lean`, `Beluga/Patterns.lean`, `Mysticeti/Safety.lean` (L10) | `quorumIntersection`, `certified_unique`, `lemma10_round_robin_pigeonhole` all sorry-free |

Round 3a (`d724efd2`) returned with a major *discovery* rather than
proofs (see F-1 below). Round 3b (`af54716b`) was cancelled to free
`Beluga/Theorems.lean` for the F-1 restatement.

## Paper-side findings (collected into [`docs/mechanization-findings.md`](../docs/mechanization-findings.md))

Eight stable findings recorded, with severity and address-status
in a summary table at the top of the file.

- **F-1 (High):** Paper L1, L2 don't follow from stated assumptions;
  the prose proofs silently use a scheduler-fairness step. Surfaced
  as `SchedulerFairness` hypothesis on L1, L2, T1–T4, corollary.
  Standalone deep-dive in
  [`docs/paper-feedback-l1-l2-fairness.md`](../docs/paper-feedback-l1-l2-fairness.md).
- **F-7 (High):** T7's prose proof slips a liveness ingredient
  (decision completeness) and a definitional move (order-from-view
  separation) into a safety claim. Currently the only finding
  **not addressed** — proof currently passes via two non-paper
  hypotheses; restatement pending user decision.
- **F-5 (Medium):** Four protocol invariants the paper treats as
  obvious are now explicit hypotheses on L13, L16, T7.
- **F-2 (Medium):** Resolved — `n = 3f+1` pinned explicitly.
- **F-3 (Medium):** Resolved — `NoEquivocationInParents` cross-block
  form added.
- **F-4 (Low):** Fully fixed — `LatencyTriangle` explicit, L4/L5 proved.
- **F-8 (Low):** Resolved — contiguous-IDs hypothesis added to L10.
- **F-6 (Low):** Documentation only.

## Definition / statement work

- New `SchedulerFairness` predicate in `Beluga/Theorems.lean`
  (round-level shadow of paper Assumption 2).
- New `LatencyTriangle` predicate in `Beluga/PerformanceLemmas.lean`
  (paper Assumption 1 made explicit).
- New `Reaches.trans` lemma in `Mysticeti/Safety.lean`.
- Four new protocol-invariant hypotheses on L13, L16, T7
  (Mysticeti/Safety.lean).
- New helper module `Beluga/StepPreservation.lean` (round-monotonicity,
  validator-persistence, action-level preservation).
- `Beluga/Theorems.lean` rewritten: L1, L2, T1–T4 take
  `SchedulerFairness`; helper-lemma signatures from the r3a
  discovery preserved with bodies sorry-stubbed where Aristotle's
  proof hit heartbeat limits in our build context.

## Build state

`lake build` passes (6244 jobs). Sorry count: 27 → 20.

| File | Before | After | Change |
|---|---|---|---|
| `Quorum.lean` | 1 | 0 | −1 |
| `Beluga/Patterns.lean` | 1 | 0 | −1 |
| `Beluga/StepPreservation.lean` (new) | — | 0 | (closed in 3e-followup) |
| `Mysticeti/Safety.lean` | 4 | 1 | −3 (only L10's sorry remained → closed; r6 added 0) |
| `Beluga/Theorems.lean` | 6 | 8 | +2 (new r3a sorry-stubs for `step_preserves_validator_ids`, `step_round_monotone`) |
| (others unchanged) |  |  |  |

L4 and L5 are now ✅ sorry-free; the §5 main theorems and corollary
are stated paper-faithfully but bodies are pending (round 3a-followup
in flight as `58873be7`).

## Doc reorganisation

- Two stale docs deleted:
  - `docs/aristotle-round3-plan.md` — pre-execution plan, all batches
    now executed/integrated.
  - `docs/formalization-status.md` — duplicative with the paper→code
    map at the top of `formalization.md`, last updated 2026-04-25.
- New: `docs/mechanization-findings.md` (paper-side findings log),
  `docs/paper-feedback-l1-l2-fairness.md` (F-1 deep dive),
  `docs/blog-aristotle-integration-gotchas.md` (operational blog seed
  for integrating Aristotle output, twenty gotchas).
- `formalization.md`, `README.md`, `CLAUDE.md`, `formalization-plan.md`,
  `blog-aristotle-integration-gotchas.md`, `Beluga/Protocol.lean`,
  `Beluga/Pull.lean`: cleaned up references to the deleted docs.
- `formalization.md` table:
  - Removed agentic-bookkeeping leakage (no project IDs / round
    numbers in the paper→code table).
  - Removed `sorry` literals from prose (using "pending" / "incomplete"
    instead, per CLAUDE.md hygiene rule).
  - Status legend gains ⚠️ (proved-but-with-paper-faithfulness-concerns,
    pointing to `mechanization-findings.md`).

## CLAUDE.md updates

- New rule: *Always update `formalization.md` after each proof round*
  — keep the status fresh, propagate ✅ through corollaries, document
  side conditions in the consistency notes, don't bleed agentic
  bookkeeping into the table.
- Sorry-comment hygiene section promoted from informational note to
  HARD RULE with explicit prohibition list.
- "Where to find what" table updated (deletions + new docs).

## Aristotle in flight at end of session

- `4cda6cb1` (round 2) — **completed and integrated this session**.
- `a8889396` (round 4): `step_refines_HonestStep` in `Beluga/Protocol.lean`.
- `d32908b4` (round 5): 11 helper lemmas in `Mysticeti/Liveness.lean`.
- `58873be7` (round 3a-followup): L1, L2, T1–T4 in `Beluga/Theorems.lean`
  under `SchedulerFairness`, plus 2 sorry-stubbed helpers from r3a.

## What's next

- Wait for the three in-flight rounds to return.
- Address F-7 (decide on T7 restatement option 1, 2, or 3 from
  `mechanization-findings.md`).
- After all rounds complete, resolve any remaining transitive
  sorries through targeted follow-up rounds.
- Eventually: derive the F-5 protocol invariants (`h_cert_base`,
  `h_dag_parent`, etc.) from the protocol structure rather than
  passing them as hypotheses.
