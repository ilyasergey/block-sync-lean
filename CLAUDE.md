# CLAUDE.md — project startup brief

Read this on every session start and after compaction. It captures the
operational state and workflows that keep this formalization moving without
repeating mistakes.

## What this project is

A Lean 4 formalization of [*Beluga: Block Synchronization for BFT Consensus
Protocols*](docs/round-01/Block_Sync_Project.pdf). For the project-wide overview
including the paper→code map, see [formalization.md](formalization.md).

Lean toolchain: **`leanprover/lean4:v4.28.0`**, matching Aristotle's pinned
version. Mathlib at commit `8f9d9cff…`. Build: `lake build`. Run:
`lake exe blocksynchroniser`.

## Two-track workflow: hand-prove + Aristotle delegation

Proofs come from two sources:

- **Hand-proved**: definitions, the four Definition-1 properties,
  validation scaffolding (Validation.lean's realizability + anti-witness
  lemmas), one-liners (`rfl`/`simp`/`decide`/`omega`), and `Lib/`
  helpers when the math is short and the Lean idiom is obvious.
- **Aristotle (Harmonic)**: substantive proofs where the bottleneck is
  Lean tactic plumbing (the *math tactical wall* — see
  [docs/math-tactical-wall.md](docs/math-tactical-wall.md)).

**Default to delegation** for any proof beyond ~10 trivial lines. Hand
attempts that hit Mathlib API discovery should be cut short.

## The Aristotle workflow (single source of truth)

Operational details live in [docs/aristotle-workflow.md](docs/aristotle-workflow.md).
Read it before submitting. Key points:

- **Submit**: `aristotle submit "<targeted prompt>" --project-dir . --wait
  --destination /tmp/aristotle-<scope>-$(date +%s).tar.gz`. Use
  `run_in_background: true` so the harness notifies on completion.
- **Targeted prompts**: name the specific theorems by their identifier and
  file, and explicitly say "leave all other sorries unchanged." This is
  the *narrow-scope* mechanism. (The earlier `sed sorry → admit` trick
  doesn't work in Lean 4 — `admit` is a synonym for `sorry`.)
- **File freezing**: while a project is in flight, *do not edit any
  file containing a target sorry*. Edit other files freely. Track frozen
  files in [docs/aristotle-projects.md](docs/aristotle-projects.md).
- **Concurrent submissions are OK**: Aristotle accepts multiple parallel
  projects per account. We've run 7 in flight at once.
- **Integration recipe**: see scripts/aristotle-integrate.sh and the doc.
  Always extract to a sandbox, diff, copy *only the target files* (other
  diffs in the tarball are typically your own later changes — Aristotle
  tarballs reflect the project state at submission time, not at result
  time).
- **Provenance markers**: every Aristotle-filled proof carries
  `-- proof: aristotle (project <id-prefix>)` immediately above. Helper
  lemmas added by Aristotle get one too (or share a section header).
  This makes `git blame` and `grep -r "proof: aristotle"` informative.
- **Attribution doc**: append a section to
  [docs/aristotle-attributions.md](docs/aristotle-attributions.md) per
  completed project. This is the source for the eventual final report.

### Iteration loop (when results return with remaining sorries)

If Aristotle returns `COMPLETE_WITH_ERRORS` with leftover sorries, **do not
just resubmit**. Diagnose every remaining sorry first.

Categories:
1. **Tactical-wall continuation** — Aristotle ran out of budget on Mathlib
   unification mid-proof. Refine the `PROVIDED SOLUTION` with specific
   Mathlib lemma names, resubmit.
2. **Semantic gap** — the executable definition doesn't satisfy the
   relational spec it's being refined against. Either tighten the
   executable, weaken the spec, or parameterize over a well-formedness
   invariant. Human judgment.
3. **Missing well-formedness invariant** — proof needs a structural fact
   true by construction but not in the theorem signature (e.g., "all
   validators in this state are system-registered"). Add the hypothesis,
   establish it from the construction, resubmit.

**Bundle every fix into a single edit pass** before resubmitting.
Resubmitting with some gaps unaddressed is a poor return on the round
(each round = ~1h wall-clock). Spend 10–30 min diagnosing all gaps.

**Delete Aristotle's incomplete proof body** before resubmitting — the
structural shape was likely valid for the *old* statement; leaving it
in place after edits will confuse the next run. Reset to plain `sorry`.

The full iteration pattern is documented in
[docs/aristotle-workflow.md § Iteration loop](docs/aristotle-workflow.md).

## Concurrency rule (file-disjoint freezing)

When multiple Aristotle projects are in flight simultaneously, the rule:

> Each in-flight project freezes the file(s) containing its target
> sorries. Edit *only* files outside the union of frozen-file sets.

The freeze map is maintained in
[docs/aristotle-projects.md](docs/aristotle-projects.md) under "Active".
Update on every submission and completion.

If you must edit a frozen file urgently, run `aristotle cancel <id>`
first; do not silently edit while a submission is processing.

## Sorry-comment hygiene (HARD RULE)

**Never write the word `sorry` in any comment, docstring, or prose
in `.lean` files (or `.md` files describing them).** The literal token
`sorry` may appear *only* as a tactic in `:= by sorry` proof
obligations. We use `grep -rn 'sorry' BlockSynchroniser/` to count
remaining proof obligations precisely; any `sorry` in prose pollutes
that count and leads to wrong status reports.

In prose, use one of: "stub", "pending", "queued", "incomplete",
"unproved", "left open", "deferred". When describing *what* is at a
proof obligation, refer to it as "a proof obligation" or "the
remaining gap".

This rule applies to:
- doc comments above theorems
- file-header `-/ ... /-` blocks
- `--` line comments inside proofs
- Markdown changelogs, plans, and tracker entries

If Aristotle's output contains the word `sorry` in a comment, strip it
during integration.

## Where to find what

| Doc | Purpose |
|---|---|
| [formalization.md](formalization.md) | Project-wide overview + paper→code map |
| [docs/formalization-plan.md](docs/formalization-plan.md) | Phased plan, scope decisions |
| [docs/aristotle-workflow.md](docs/aristotle-workflow.md) | Aristotle delegation operational manual |
| [docs/aristotle-projects.md](docs/aristotle-projects.md) | Live in-flight / queued / completed Aristotle submissions |
| [docs/aristotle-attributions.md](docs/aristotle-attributions.md) | Per-project attribution log (for final report) |
| [docs/math-tactical-wall.md](docs/math-tactical-wall.md) | The wall-vs-gap concept (blog seed: conceptual) |
| [docs/blog-aristotle-integration-gotchas.md](docs/blog-aristotle-integration-gotchas.md) | Operational gotchas integrating Aristotle output (blog seed: practical). **Append new findings here as they come up.** |
| [docs/round-01/mechanization-findings.md](docs/round-01/mechanization-findings.md) | Paper-side log of observations the formalization surfaced (paper terminology only, for folding back into the paper). **Append new findings here when mechanization reveals a paper-relevant gap or ambiguity.** |
| [docs/round-01/paper-feedback-l1-l2-fairness.md](docs/round-01/paper-feedback-l1-l2-fairness.md) | Deep dive on F-1 (scheduler fairness for L1/L2). |
| [docs/final-report-outline.md](docs/final-report-outline.md) | Report skeleton |
| [changelogs/](changelogs/) | Per-stage timestamped changelogs |
| [changelogs/2026-04-25-session-narrative.md](changelogs/2026-04-25-session-narrative.md) | Cross-phase decision threads |
| [scripts/aristotle-integrate.sh](scripts/aristotle-integrate.sh) | Integration helper |

## Build state at last session

If `lake build` is dirty, look at last commit's changelog for the cause
and fix the imports / definitions before doing other work. The library
must compile cleanly except for expected `sorry` warnings.

`Validation.lean` and `Mysticeti/Liveness.lean` import `Mathlib.Tactic`
(narrowed from Aristotle's auto-added `import Mathlib`) — this is
required to keep the clang executable-link command under the OS
arg-limit. Don't widen back to `import Mathlib`.

## Commit conventions

- One commit per logical step (Phase, sub-phase, integration round).
- Commit messages explain what changed and *why*, not just what files
  were touched.
- Commit Aristotle integrations separately from manual work, with the
  project ID in the message.

## Always update formalization.md after each proof round

[formalization.md](formalization.md) is the single source of truth for
the paper→code map and per-item status. **Every Aristotle integration
or hand-proof commit that changes the proof state of a paper item must
update the corresponding row in formalization.md.**

Update rules:

- A row's status (✅ / ◐ / ☐ / ⊘ / ⏸) reflects the *current* proof
  state, not the submission state. ✅ means *all dependencies are
  proved*; ◐ means body proven but at least one transitive dependency
  is `sorry`; ☐ means stated but no proof body yet.
- Don't bleed Aristotle bookkeeping into the table — no project IDs,
  no round numbers, no "in flight" notes. Those live in
  [docs/aristotle-projects.md](docs/aristotle-projects.md) and
  [docs/aristotle-attributions.md](docs/aristotle-attributions.md).
  formalization.md is read by people who care about *paper conformance
  and proof state*, not the agentic workflow.
- When a proof closes that a corollary depends on, *also* update the
  corollary's row (e.g., closing T1–T4 promotes
  `belugaTrace_isBlockSynchronizer` from ◐ to ✅).
- New paper-faithful side conditions (e.g., `LatencyTriangle`,
  `BelugaState.WellFormed`) get an entry in the "Notes on paper
  consistency" section.

## Always update the changelog

**Every commit that lands a phase / sub-phase / Aristotle integration /
iteration / definition repair / discovery should be paired with a
changelog entry.** Changelogs are how the project's history is
reconstructable — without them, six months from now nobody will know
why a definition has its current shape.

Conventions:
- File path: `changelogs/YYYY-MM-DD-<topic>.md`. Topic is short and
  scope-specific, e.g. `phase-4-protocol-modules`,
  `aristotle-round1-integration`, `iterate-on-r3f-paper-consistency`.
- Each entry covers: what changed (technical), why (decision /
  diagnosis), build state (jobs, sorries), Aristotle attributions
  (project IDs of any work integrated), what's next.
- For decisions that span multiple commits, also append to
  `changelogs/2026-04-25-session-narrative.md` (the cross-phase
  thread doc).
- See [`changelogs/README.md`](changelogs/README.md) for the
  long-form conventions.

If you skip a changelog entry, the next session won't have the
context to continue. **Don't.**

## Default working pattern

1. Read CLAUDE.md (this file) and any pending notifications about
   Aristotle results.
2. Check [docs/aristotle-projects.md](docs/aristotle-projects.md) for
   in-flight state.
3. Decide: integrate a returned result, or iterate, or do hand-proof
   on free files.
4. After every change: `lake build`, then commit with a clear message,
   then update changelogs / status if appropriate.
5. Stop and ask the user when entering a new phase or making
   destructive operations (`rm -rf .lake`, force-pushing, etc.).
