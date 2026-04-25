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

## Open questions / what's left

- **Sub-phase 4e** (next): `HonestStep` relational small-step + executable
  `step` function + refinement lemma. The substantive part of Phase 4.
- **Aristotle integration** (whenever `be7c0245-…` returns): extract,
  diff, review, apply, verify, attribute, commit. Per the operational
  recipe.
- **Aristotle round 2**: queue is `quorumIntersection` (Quorum.lean) and
  `certified_unique` (Patterns.lean). Eligible to fire in parallel with
  4e once the round-1 result is integrated and `Validation.lean` is
  unfrozen.
- **Validation note**: the small Trace.lean change (Decidable instances)
  is unrelated to Aristotle's task and shouldn't conflict on integration.
  Worth verifying when the diff comes back.

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
