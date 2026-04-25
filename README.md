# BlockSynchroniser

A Lean 4 formalization of [*Beluga: Block Synchronization for BFT Consensus
Protocols*](docs/Block_Sync_Project.pdf).

> 📖 **Start here: [formalization.md](formalization.md)** — overview of what we're
> building, the repository layout, the distinction between paper theorems and
> validation lemmas, and pointers to the deeper docs.
>
> 📝 **Paper feedback: [docs/mechanization-findings.md](docs/mechanization-findings.md)** —
> running log, in paper terminology only, of issues the formalization
> surfaced about the Beluga paper (missing assumptions, scope ambiguities,
> implicit invariants). This is the working list of edits we plan to
> propose to the paper authors.

## What this is

A formal model of a block synchronizer for BFT consensus: validators
collectively build a structured, ever-growing set of blocks while tolerating
up to `f` Byzantine validators out of `n ≥ 3f + 1`. The four properties of
Definition 1 (Round-Progression, Round-Termination, Block availability,
Causal availability) are the load-bearing definitions; the rest of the
formalization either supports them, validates them, or proves the Beluga
protocol satisfies them.

## Build

```bash
lake update
lake build
```

Requires Lean 4 toolchain `leanprover/lean4:v4.28.0` (pinned in
[`lean-toolchain`](lean-toolchain)). The `lake update` step pulls Mathlib
and Batteries; the `lake build` step uses Mathlib's cloud cache to avoid
recompiling Mathlib from scratch.

## Documentation map

### For the paper authors

| Document | Purpose |
|---|---|
| [docs/mechanization-findings.md](docs/mechanization-findings.md) | **Running list of paper-side observations from the formalization.** Paper terminology only; the working list of edits to propose to the authors. |
| [docs/paper-feedback-l1-l2-fairness.md](docs/paper-feedback-l1-l2-fairness.md) | Standalone deep dive on finding F-1 (scheduler fairness for Lemmas 1 & 2). Self-contained, no Lean. |
| [docs/Block_Sync_Project.pdf](docs/Block_Sync_Project.pdf) | The paper itself. |

### Project overview

| Document | Purpose |
|---|---|
| [formalization.md](formalization.md) | **Overview & entry point** — paper→code map, Lean-side modeling notes, repository layout. |
| [docs/formalization-plan.md](docs/formalization-plan.md) | Phased plan, file layout, scope decisions. |

### Workflow & process

| Document | Purpose |
|---|---|
| [docs/aristotle-workflow.md](docs/aristotle-workflow.md) | Operational manual for delegating proofs to Aristotle (Harmonic). |
| [docs/aristotle-projects.md](docs/aristotle-projects.md) | Live tracker of in-flight / completed Aristotle submissions. |
| [docs/aristotle-attributions.md](docs/aristotle-attributions.md) | Per-project attribution log — which proofs were filled by Aristotle and how. Source for the eventual final report. |

### Notes worth posting publicly (blog seeds)

| Document | Purpose |
|---|---|
| [docs/math-tactical-wall.md](docs/math-tactical-wall.md) | Conceptual seed: when to delegate Lean proofs vs hand-prove, framed around the *math tactical wall* — the moment where math is done and only Lean plumbing remains. |
| [docs/blog-aristotle-integration-gotchas.md](docs/blog-aristotle-integration-gotchas.md) | Operational seed: 20 concrete gotchas integrating Aristotle output into a real Lean repository. Companion to the wall doc. |

### History

| Document | Purpose |
|---|---|
| [changelogs/](changelogs/) | Per-stage timestamped changelogs. Most recent first. |
| [changelogs/2026-04-25-session-narrative.md](changelogs/2026-04-25-session-narrative.md) | Cross-phase decision threads spanning multiple commits. |
| [docs/final-report-outline.md](docs/final-report-outline.md) | Skeleton for the eventual write-up. |

## Project structure

```
block-sync-lean/
├── BlockSynchroniser/          # Library modules (per-concept files)
├── Main.lean                   # Driver (executable Beluga lands in Phase 4)
├── docs/                       # Plan, status, workflow notes; the paper
├── changelogs/                 # Per-stage changelogs
├── formalization.md            # Overview & entry point
└── README.md                   # This file
```

See [formalization.md](formalization.md#repository-layout) for the per-file
breakdown.

## License

Apache License, Version 2.0 — see [LICENSE](LICENSE).
