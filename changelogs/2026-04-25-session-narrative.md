# 2026-04-25 — Session narrative

A meta-changelog capturing the *exploration and decision threads* that
span this session's commits. Phase-level technical changelogs cover *what*
changed; this entry covers *why*, *what was considered and abandoned*,
and *what's left open*.

Read this alongside the per-phase changelogs to reconstruct the
conversational arc.

## Context at session start

- Project at Lean v4.23.0 with `ssreflect` as a hard dep; existing
  `Definitions.lean` had four Definition-1 properties under legacy names
  (`blockSynchroniserProgressI/II`, `blockSynchroniserAvailability`,
  `blockSynchroniserCausalAvailability`), plus a `blockSynchroniserValidity`
  and `blockSynchroniserCommonSet` that were *not* in paper Definition 1.
- A typo at line 228 (`state_kz`) discovered then corrected upstream.
- Two orphan ssreflect files in `BlockSynchroniser/Existing/` not imported
  by the build.

## Major decisions and threads

### Toolchain bump → v4.28.0 (commit `aff16da`)

Reason: align with **Aristotle's pinned Lean version** (`v4.28.0`,
Mathlib commit `8f9d9cff…`). Without this match, Aristotle submissions
risk compatibility breaks on either side. Side effect: `lean-ssr` master
is on v4.26.0, so ssreflect would no longer compile against v4.28.0; the
`require ssreflect` line in `lakefile.lean` was commented out (user did
this), and the orphan ssreflect files in `Existing/` were deleted in
Phase 0.

### Veil considered, deferred

The user pointed at a sibling Veil project at v4.27.0 with
`veil-2.0-preview` branch as a possible dependency for model-checking-
style validation. Assessed:

- **Strong conceptual fit**: Veil's BcastByz, FloodSet, and Blockchain
  examples cover Byzantine quorum protocols closely matching Beluga's
  shape.
- **Hard version conflict**: Veil at v4.27.0 cannot coexist with our
  v4.28.0 + Aristotle dependency in a single Lake project.
- **Recommendation**: companion sibling project `block-sync-veil/`
  (separate repo, separate toolchain) for model-check validation only.
- **Decision**: deferred. User said "let's not bother with Veil for now."
  Documented as future option in the plan.

The interesting bit for posterity: Veil's `#model_check { node := Fin 4 }`
exactly matches the `goldenTrace`-style validation we ended up building
by hand. If we ever revisit, Veil would *strengthen* layer (D) of the
non-vacuity strategy from "decidable smoke tests" to "exhaustive
small-state model checking."

### "Two kinds of theorems" clarification

The `golden_*` theorems in `Validation.lean` initially looked like paper
results, which prompted the user to ask "what do those correspond to in
the paper?" — and they don't. They're **internal sanity checks** that
our formalization isn't vacuously true.

Surfaced this distinction by:
- Opening comment block in `Validation.lean` explicitly stating it.
- A "Two kinds of theorems" section in
  [`formalization.md`](../formalization.md) (now relegated below the
  paper map).
- A section in [`docs/formalization-status.md`](../docs/formalization-status.md).

The user later asked the *same* question about `certified_unique` —
which prompted a citation fix (it's paper §4.4 informal uniqueness
consequence, *not* Appendix D Lemma 15; Lemma 15 is a specialization to
leader blocks).

This led to a project-wide policy: **every substantial paper-aligned
definition / lemma / theorem must carry an explicit citation in its
docstring, and `formalization.md` must hold the master map prominently
at the top.**

### Validation strategy — three layers

Settled on three layers of non-vacuity defense, in order of effort:

- **(A) goldenTrace satisfaction**: a concrete honest-synchronous trace
  proved to satisfy all four Def-1 properties non-trivially. Stated;
  proofs deferred to Aristotle.
- **(B) Realizability**: for each `P → ∃ Q` property, an existence
  lemma showing `P` is reachable. Hand-proved.
- **(C) Anti-witnesses**: `emptyTrace` proved to *fail* at least one
  property. Hand-proved.

### Aristotle delegation policy

Refined twice:

1. First pass: hand-first, delegate-when-stuck.
2. User refinement: "set yourself a small limit on attempts and delegate
   sorry'd proofs more aggressively so you won't run out of tokens";
   "make sure that you delegate to Aristotle the proofs in files you're
   not going to touch yourself while working concurrently."

Codified in [`docs/aristotle-workflow.md`](../docs/aristotle-workflow.md):

- Attempt budget: one-liners always tried; ≤ 10 lines gets one ~5 min
  attempt then delegate; medium gets a sketch then delegate; bigger
  delegated immediately.
- Concurrency rule: files under in-flight submission are *frozen*; work
  on disjoint files in parallel.
- Cancel-rather-than-conflict: if I urgently need a frozen file, cancel
  the project rather than risk a merge mess.
- Operational recipe: submit → sandbox-extract → diff → review → apply
  → verify → annotate-and-commit, with provenance markers
  `-- proof filled by Aristotle (project <id>)`.

### Aristotle project tracker

User asked: "Are you keeping a map which Aristotle queries are
responsible for which files/theorems to complete?" Answer at the time:
no, only informal mentions. Created
[`docs/aristotle-projects.md`](../docs/aristotle-projects.md) — central
single-source-of-truth for active / queued / completed submissions.

### "Can we run the protocol?" — Phase 4 commitment

User asked whether we can run the protocol at the current stage. Answer:
no, only data types and specifications. Discussed:

- Option A: Phase-2 shortcut — minimal honest-synchronous step function
  (~300 LOC) just to seed `goldenTrace`.
- Option B: defer runnability until Phase 4 (the real protocol) which
  will include both a relational `HonestStep` for theorems *and* a
  computable `step` for execution.

Decided B (cleaner; no throwaway LOC). Locked into the plan: "Phase 4
ships executable `step` + refinement lemma alongside the relational
`HonestStep`."

### Concurrency demonstration (sub-stage 2.5 + Phase 3, then 4a–4d)

User said "let's do option 1. I'm curious to see how concurrency works
in our case." Submitted Aristotle project
`be7c0245-cdb9-4cce-9c4a-fffecfd1a69c` (the four `golden_*` theorems in
`Validation.lean`); started Phase 3 in parallel; on its tail Phase 4
sub-phases 4a (`BelugaState`), 4b (`Reputation`), 4c
(`AdmissionControl`), 4d (`Pull`) all landed without touching the
frozen `Validation.lean`.

So far the concurrency rule has held: my edits (and a small Trace.lean
adjustment for `Decidable` instances) only triggered transitive
recompiles of `Validation.lean`, never source-level edits.

Aristotle remains IN_PROGRESS at ~2% on this project as of Phase 4d
commit (`3a2d934`). Slow burn.

## Continuing threads (added in second half of session)

### "Write full implementations, omit proofs"

User course-correction during sub-phase 4e: my first cut had `step s = s`
as a placeholder. Replaced with a real round-robin implementation
(scan validators in id order; first-applicable action; priority
propose → accept → store → advance). See `7c044a9` and the
[continuation changelog](2026-04-25-session-continuation-phases-4e-onward.md).

### Runnable examples

Triggered by user's "Do we have executable examples?" Built
`BlockSynchroniser/Beluga/Examples.lean` (system4, run, reprLog,
proposersFor, `#eval` smoke tests) and turned `Main.lean` into a real
driver. `lake exe blocksynchroniser` now prints a real 20-step Beluga
trace. Documented at the top of `formalization.md`.

### Phase 5 — main theorems stated

Six theorems (L1, L2, T1, T2, T3, T4) stated against `belugaTrace`,
each with a verbatim `PROVIDED SOLUTION` from the paper. L1, L2 were
initially abstract (`∃ k`); refined in Phase 4.5 with timing.

### Phase 6 — Mysticeti-Beluga safety bundle

Decision rules (paper App D.1.1) and round-robin leader schedule
(D.1.2) implemented in full. Safety lemmas L10, L13, L14, L15, L16,
T7 stated. **L15 is the only one I closed by hand** (`certified_unique`
specializes to leader blocks where author is fixed by the schedule).
Everything else has paper sketches awaiting Aristotle.

### Two kinds of theorems — citation policy adopted

User asked: "What does `golden_roundProgression` correspond to in the
paper?" Answer: nothing — it's internal validation. Then: "What about
`certified_unique`?" Answer: paper §4.4 (not Appendix D Lemma 15 as I
had said). Triggered:

- A clarifying comment block at the top of `Validation.lean`.
- A "Two kinds of theorems" section in `formalization.md`.
- Project-wide policy: every paper-aligned definition / lemma / theorem
  carries an explicit paper citation in its docstring.
- Restructured `formalization.md`: paper→code map at the very top,
  before repository layout / two-kinds explanation.

Audit pass added missing citations to `Quorum.lean` (BFT
quorum-intersection — *not* paper-numbered but standard) and to
`Properties.lean :: BlockSynchronizer` (Definition 1, paper §2.1
conjunction).

### Liveness path opened — Phase 4.5

User: "Why can't we do liveness facts and appendix C lemmas?" → "add
the necessary bits for liveness. No probabilities so far."

Diagnosis: blockers were structural, not effort-level.

- **No timing model** — `Trace = Nat → S` indexes by step number, not
  wall-clock time. L1/L2 are wall-clock claims, so they had been
  stated with abstract `∃ k`.
- **`ByzantineStep := True`** — too permissive; refinement allows
  Byzantine validators to do *anything*, including impersonate honest
  ones, breaking proofs.

Phase 4.5 added `BlockSynchroniser/Timing.lean` with `TimeMap`,
`Monotone`/`Unbounded`/`WellFormed` predicates, and
`PartiallySynchronous` (post-GST trace advances time ≤ Δ per step).
Then refined L1/L2 to use it; added App D liveness bundle (L8, L9,
L11, L12, T6) in `Mysticeti/Liveness.lean`, all with paper sketches.

### ByzantineStep refinement — Phase 4.5b

Triggered by user's "Are we going to revise Byzantine behaviours from
True to something more meaningful?" Yes. New definition: monotone
op-log extension where every newly-emitted op is attributable to a
Byzantine validator. Made the trivial `step_refines_HonestStep` proof
fail; replaced with a `sorry` + detailed case-analysis sketch.

### App C deterministic L3, L4, L5 — Phase 4.5b

Triggered by user's "Have we done this? Lemmas 3, 4, 5 — deterministic
worst-case latency bounds…" — prereqs were now in (timing + Byzantine
constraint), but statements weren't yet in the code. Added in new file
`BlockSynchroniser/Beluga/PerformanceLemmas.lean`. Probabilistic L6, L7,
T5 remain ⊘ (would need a probability framework — explicitly
acknowledged at multiple places).

### Aristotle project tracker created

Triggered by user's "Are you keeping a map which Aristotle queries are
responsible for which files/theorems to complete?" Answer at the time:
no, only informal mentions. Created
[`docs/aristotle-projects.md`](../docs/aristotle-projects.md) — central
single-source-of-truth for active / queued / completed submissions.

### Detailed-changelog policy adopted

Triggered by user's "Are you maintaining changelogs? Make them very
detailed so the rough history of this exploration/conversation could
be restored." This narrative file plus per-phase changelogs are the
result. Phase entries now capture decisions/discussions, not just
code changes; narrative entries capture cross-phase threads.

### Proof effort plan + the math tactical wall

After all the structural work landed, the user asked for a proof-effort
plan ordered simplest-to-hardest, to be executed in small steps with
commits after each. The plan (in
[the session-continuation changelog](2026-04-25-session-continuation-phases-4e-onward.md))
ordered by mathematical simplicity — but the first two attempts (Lemma
10, `quorumIntersection`) immediately revealed the same pattern:

> The math is in the docstring. What's left is the Lean plumbing —
> figuring out the right `Finset.*` lemma, massaging types,
> getting the goal into the shape some Mathlib lemma expects. Tedious
> for a human, fast for Aristotle.

Both got prepped (statement strengthened, sketch refined) and queued
for Aristotle round 2 instead of hand-proved.

I named this pattern the **math tactical wall**: the moment in a proof
where the bottleneck shifts from math content to tactic plumbing. It
became the load-bearing concept for our human/AI division of labor.
The user liked the framing and asked me to document it prominently as
seed for a future blog post. Result:
[docs/math-tactical-wall.md](../docs/math-tactical-wall.md) — a
stand-alone note with definition, why-it-matters, worked example,
decision cues, and a pitch.

Cross-references added: [`docs/aristotle-workflow.md`](../docs/aristotle-workflow.md)
(in delegation policy), [`formalization.md`](../formalization.md)
(in "Where to look").

## Open proof-effort threads

- **Step 1**: Lemma 10 — prepped, queued for Aristotle round 2.
- **Step 2**: `quorumIntersection` — prepped, queued for Aristotle
  round 2.
- **Step 3 (done)**: `certified_unique` — content gap fixed
  (`NoEquivocationInParents` strengthened from within-block to
  cross-block). Proof itself queued for Aristotle round 2 (depends on
  `quorumIntersection`). This step is the counter-example to "always
  delegate the wall" — the issue here was math content, not Lean
  plumbing; Aristotle would have produced an invalid or incomplete
  proof.

## Pattern emerging: walls vs. gaps

Three steps in, the proof effort has revealed a clean dichotomy:

- **Tactical wall** (step 1, step 2): math is in the docstring, plumbing
  remains. Aristotle's job. Prep + queue, move on.
- **Content gap** (step 3): a hidden mismatch between the lemma's
  hypotheses and the proof structure that can only be seen by working
  the math through. Human's job. Strengthen statement, *then* delegate.

This is captured in the decision-cue table at
[docs/math-tactical-wall.md § When to push through anyway](../docs/math-tactical-wall.md).

## Open questions / what's left

- **Aristotle round 1** (`be7c0245-…`, IN_PROGRESS at ~26%): integrate
  when it returns. Per the operational recipe in
  [`docs/aristotle-workflow.md`](../docs/aristotle-workflow.md).
- **Aristotle round 2**: queue is `quorumIntersection`,
  `certified_unique`, `lemma10_round_robin_pigeonhole` (pure
  combinatorics), and the easier App D safety pieces (L13, L14, L16, T7).
  Eligible to fire in parallel once round 1 unfreezes
  `Validation.lean`.
- **Aristotle round 3** (further out): the timing-flavored proofs
  (L1, L2, L8, L9, L11, L12, T6) and App C L3/L4/L5. Heavier — these
  rely on the timing model + refined Byzantine semantics in non-trivial
  ways.
- **Hand-prove candidates**: `step_refines_HonestStep` (case analysis on
  step's findSome? result + each `tryActFor` branch). Other Lemma 10
  could be hand-proven (pure `Fin.range` pigeonhole) but feels slightly
  delicate.
- **Validation note**: the Trace.lean change (Decidable instances)
  added during Phase 4c is unrelated to Aristotle's in-flight task and
  shouldn't conflict on integration. Worth verifying when the diff
  comes back.
- **Outstanding skeleton conclusions**: a few statements have placeholder
  `True` conclusions (Lemma 13's "B' references a certificate for B"
  predicate, Lemma 14's "no honest skip", Lemma 16's "consistent
  decision", Theorem 6's "ordered/finalized", Theorem 7's "consistent
  ordering"). These need a per-validator consensus-state data
  structure, deferred to a follow-up phase.

## Files added this session (in order)

- `docs/Block_Sync_Project.pdf` (user-committed earlier)
- `docs/aristotle/*.pdf` (user-downloaded; gitignored)
- `docs/aristotle-workflow.md`
- `docs/formalization-plan.md`
- `docs/formalization-status.md`
- `docs/aristotle-projects.md`
- `formalization.md` (top-level, paper→code map)
- `BlockSynchroniser/{Block,Validator,Operations,System,State,Causal,
  Quorum,Trace,Properties,Validation}.lean` (Phase 1 + 2 split)
- `BlockSynchroniser/Beluga/{BlockExt,Patterns,State,Reputation,
  AdmissionControl,Pull}.lean` (Phase 3 + 4a–4d)
- `changelogs/*.md` (this and prior entries)

Files removed:
- `BlockSynchroniser/Definitions.lean` (decomposed in Phase 1)
- `BlockSynchroniser/Existing/{DAGBasedCertified,DAGBasedOPT}.lean` and
  `Scratchpad.txt` (orphan ssreflect exploration; Phase 0)
