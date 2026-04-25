# BlockSynchroniser

A Lean 4 formalization of [*Beluga: Block Synchronization for BFT Consensus
Protocols*](docs/Block_Sync_Project.pdf).

> 📖 **Start here: [formalization.md](formalization.md)** — overview of what we're
> building, the repository layout, the distinction between paper theorems and
> validation lemmas, and pointers to the deeper docs.

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

| Document | Purpose |
|---|---|
| [formalization.md](formalization.md) | **Overview & entry point** |
| [docs/formalization-plan.md](docs/formalization-plan.md) | Phased plan, file layout, scope |
| [docs/mechanization-findings.md](docs/mechanization-findings.md) | Paper-side log of observations the formalization surfaced |
| [docs/aristotle-workflow.md](docs/aristotle-workflow.md) | When and how we delegate proofs |
| [changelogs/](changelogs/) | Per-stage changelog entries |

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
