# 2026-04-25 — Session continuation: phases 4e → 6 → 4.5 → 4.5b

Picks up where
[2026-04-25-phase-4-partial-protocol-modules.md](2026-04-25-phase-4-partial-protocol-modules.md)
left off. Commit-by-commit log of the rest of the session.

## `7c044a9` — phase 4 epilogue: runnable Beluga protocol

User asked "do we have executable examples?" — answer was "infrastructure
yes, runnable demo no." This commit closes the loop.

- New file [`BlockSynchroniser/Beluga/Examples.lean`](../BlockSynchroniser/Beluga/Examples.lean):
  - `system4`: 4-validator, 1-Byzantine-budget honest system used for demos.
  - `run n`: iterate executable `step` n times from `BelugaState.init system4`.
  - `reprOp` / `reprLog`: human-readable formatting of operations.
  - `proposersFor`: distinct round-`r` proposers from the op log.
  - `#eval` smoke tests producing real, growing op logs.
- Updated [`Main.lean`](../Main.lean): drives `run 20` and prints the trace.
  Sample output now appears in [`formalization.md` § Runnable examples](../formalization.md#runnable-examples).
- Trace exhibits the round-robin scheduler's behaviour: vid 0 exhausts
  its actions before vid 1 takes over (propose → accept own → store own
  → next-validator-proposes → catch up).

## `d799b2f` — phase 5: Beluga's main theorems (paper §5)

After the user said "write full implementations, omit proofs" — stated
all six §5 results.

- New file [`BlockSynchroniser/Beluga/Theorems.lean`](../BlockSynchroniser/Beluga/Theorems.lean):
  - `lemma1_honest_round_entry` — initially abstract `∃ k`; refined in
    Phase 4.5 to use `time k ≥ system.GST + 3 * system.Δ`.
  - `lemma2_round_latency` — same; refined to `time k' ≤ time k + 3Δ`.
  - `theorem1_block_availability` — `BlockAvailability system (belugaTrace system)`.
  - `theorem2_causal_availability` — `CausalAvailability system (belugaTrace system)`.
  - `theorem3_round_progression` — `RoundProgression`.
  - `theorem4_round_termination` — `RoundTermination`.
  - `belugaTrace_isBlockSynchronizer` — one-line conjunction (no sorry of
    its own; gates on the four sorried theorems).

Each carries a verbatim `PROVIDED SOLUTION` block from the paper's prose,
ready for delegation to Aristotle.

## `cdfb3b8` — phase 6: Mysticeti-Beluga consensus + safety bundle (App D)

After confirming we'd take on Phase 6 stretch.

- New file [`BlockSynchroniser/Mysticeti/Consensus.lean`](../BlockSynchroniser/Mysticeti/Consensus.lean) (full implementations):
  - `leaderOf system r := r % system.n` (round-robin schedule).
  - `isLeaderBlock`.
  - `skipPattern` / `skipPatternB`: < 2f+1 next-round references.
  - `certificatePatternAt` / `…B`: ≥ 2f+1 next-round distinct-author
    references.
  - `Decision = ToCommit | ToSkip | Undecided` (DecidableEq derived).
  - `directDecide` (paper App D.1.1 direct decision rule).
  - `indirectDecideStep` (one-step lookahead of indirect rule;
    recursive search lives in safety proofs).
- New file [`BlockSynchroniser/Mysticeti/Safety.lean`](../BlockSynchroniser/Mysticeti/Safety.lean):
  - `lemma10_round_robin_pigeonhole` (sorry; pure combinatorics).
  - `lemma13_cert_persistence` (sorry; uses quorumIntersection).
  - `lemma14_no_skip` (sorry; uses Lemma 13 + non-equivocation).
  - `lemma15_unique_cert` — **proved** via `Beluga.certified_unique`
    (one-line; specialization of `certified_unique` to leader blocks
    where author is fixed by the leader schedule).
  - `lemma16_consistent_status` (sorry; backward induction on rounds).
  - `theorem7_consensus_safety` (skeleton; sorry).

Detour: `directDecide` initially used `Prop`-valued `skipPattern` /
`certificatePatternAt` inside `if-then-else`, which failed type-class
synthesis. Added Bool-valued `…B` variants to fix.

## `18d5c76` — phase 4.5: timing infrastructure + liveness statements

Triggered by user's "Why can't we do liveness facts and appendix C
lemmas?" → "add the necessary bits for liveness. No probabilities so
far."

- New file [`BlockSynchroniser/Timing.lean`](../BlockSynchroniser/Timing.lean):
  - `TimeMap := Nat → Nat`.
  - `TimeMap.Monotone`, `.Unbounded`, `.WellFormed` predicates.
  - `TimeMap.stepIsTime` (trivial step-equals-time map; `WellFormed`
    proven by `decide` analogue).
  - `PartiallySynchronous`: post-GST trace advances time by ≤ Δ per step.
- Refined `lemma1_honest_round_entry` and `lemma2_round_latency` in
  `Beluga/Theorems.lean` to take `(time : TimeMap) (h_time h_sync : …)`
  hypotheses and quantify over `time k ≥ GST + 3Δ` etc.
- New file [`BlockSynchroniser/Mysticeti/Liveness.lean`](../BlockSynchroniser/Mysticeti/Liveness.lean):
  - `lemma8_leader_referenced` (post-GST + 4Δ leader-block-reference
    bound).
  - `lemma9_honest_certificate` (post-GST + 4Δ certificate creation).
  - `lemma11_eventual_decision`.
  - `lemma12_referenced_accepted` (the ImPoA implicit-PoA argument).
  - `theorem6_consensus_liveness` (skeleton).

Probabilistic content (App C L6, L7, T5) remained ⊘.

## `e4f8289` — phase 4.5b: refined ByzantineStep + App C deterministic L3–L5

User asked: "Are we going to revise Byzantine behaviours from True to
something more meaningful?" — yes, we should. And: "Have we done this?
Lemmas 3, 4, 5 — deterministic worst-case latency bounds…" — no, but
prerequisites are in.

- `BlockSynchroniser/Beluga/Protocol.lean`:
  - New helper `operationAuthor : ValidatorOperation → ValidatorId`.
  - **`ByzantineStep`** refined: was `True`, now a monotone op-log
    extension `s'.emittedOperations = s.emittedOperations ++ newOps`
    where every `op ∈ newOps` has a Byzantine `operationAuthor`. Makes
    the HonestStep / ByzantineStep partition meaningful.
  - `step_refines_HonestStep` — trivial proof no longer works; replaced
    with `sorry` + a detailed `PROVIDED SOLUTION` sketch describing
    the case analysis (no-validator-can-act → empty-newOps Byzantine;
    honest action → HonestX; Byzantine action → singleton Byzantine).
- New file [`BlockSynchroniser/Beluga/PerformanceLemmas.lean`](../BlockSynchroniser/Beluga/PerformanceLemmas.lean):
  - `lemma3_honest_not_blamed` (post-GST honest reputation
    non-decreasing in honest views).
  - `lemma4_round_latency_delta` (round latency = Δ when honest reputs
    dominate).
  - `lemma5_round_latency_or_blamed` — deterministic disjunction:
    either round latency ≤ 2Δ or some malicious validator is blamed
    (≤ 3Δ). The "expected" version (paper Lemma 5) is the
    probabilistic one we don't formalize.
  - All carry verbatim `PROVIDED SOLUTION` sketches.

`formalization.md` updated multiple times during this stage:
- §5 timing rows refined.
- App D liveness rows ⏸ → ◐.
- App C row populated with code paths.
- Stale Phase 4 rows fixed (`Reputation.lean`, `AdmissionControl.lean`,
  `Pull.lean` were still showing ☐ Phase 4 even though those modules
  had landed; flipped to ✅).
- Repository layout caught up (Timing.lean, Liveness.lean, Examples.lean,
  PerformanceLemmas.lean).

## Other docs commits

- `d56931b` — fix paper citation for `certified_unique` (was
  Lemma 15; correct primary citation is paper §4.4 informal
  uniqueness consequence; Lemma 15 is a *specialization* to
  leader blocks).
- `8d85d9f` — created [`docs/aristotle-projects.md`](../docs/aristotle-projects.md)
  central tracker (active / queued / completed Aristotle submissions),
  plus a section in `aristotle-workflow.md` referencing it.
- `f673c8d` — restructured `formalization.md`: paper→code map at the
  top, repository layout / two-kinds explanation moved below; added
  explicit citations everywhere a paper item is formalized.

## Build trajectory

| Commit | Jobs | Sorries |
|---|---|---|
| (start of session) | 24 | 1 (quorumIntersection) |
| Phase 4 partial (4a–4d) | 38 | 5 |
| Phase 4 epilogue + 4e | 42 | 6 |
| Phase 5 | 44 | 12 |
| Phase 6 stubs | 48 | 14 |
| Phase 4.5 (timing + liveness) | 52 | 19 |
| Phase 4.5b (Byzantine + App C) | 54 | 25 |

Sorry growth is monotonic — every new theorem is a fresh `sorry` waiting
to be filled. Aristotle round 1 (`be7c0245-…`) currently filling 4 of
those (`golden_*` in `Validation.lean`).

## Aristotle status throughout

Project `be7c0245-cdb9-4cce-9c4a-fffecfd1a69c` was IN_PROGRESS the
entire stage. Progress trickled from 1% (Phase 4a/b) → 25% (Phase 5)
→ 26% (Phase 4.5b). At time of this changelog: still IN_PROGRESS,
~26% / 53min in.

The frozen-files rule held throughout: `Validation.lean` was never
edited locally. The only file in the project that triggered transitive
recompiles of `Validation.lean` was `Trace.lean` (added `Decidable`
instances during Phase 4c) — which is *imports*, not source-content
changes, so the freeze rule is satisfied.

## State at end of stage

Statement-level coverage of paper:

- ✅ Definition 1.1–1.4 (Properties.lean).
- ✅ §4 Beluga (BlockExt, Patterns, State, Reputation, AdmissionControl,
  Pull, Protocol, Examples) — full implementations.
- ✅ §5 Lemmas 1, 2; Theorems 1–4 — stated with PROVIDED SOLUTION sketches.
- ✅ App C deterministic L3, L4, L5 — stated.
- ✅ App D safety bundle (L10, L13–L16, T7) — stated.
- ✅ App D liveness bundle (L8, L9, L11, L12, T6) — stated.
- ⊘ App C probabilistic L6, L7, T5 — out of scope (probability framework).

Proof-level coverage: 4 in flight via Aristotle, 21 sorried with
sketches awaiting Aristotle round 2 / hand-prove.
