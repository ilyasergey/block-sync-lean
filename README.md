# BlockSynchroniser

A Lean 4 formalization of [*Beluga: Block Synchronization for BFT Consensus
Protocols*](docs/round-01/Block_Sync_Project.pdf).

> 📖 **Start here: [formalization.md](formalization.md)** — overview of what we're
> building, the repository layout, the distinction between paper theorems and
> validation lemmas, and pointers to the deeper docs.
>
> 📝 **Paper feedback: [docs/round-01/mechanization-findings.md](docs/round-01/mechanization-findings.md)** —
> running log, in paper terminology only, of issues the formalization
> surfaced about the Beluga paper (missing assumptions, scope ambiguities,
> implicit invariants).

## What this is

A formal model of a block synchronizer for BFT consensus: validators
collectively build a structured, ever-growing set of blocks while tolerating
up to `f` Byzantine validators out of `n ≥ 3f + 1`. The four properties of
Definition 1 (Round-Progression, Round-Termination, Block availability,
Causal availability) are the load-bearing definitions; the rest of the
formalization either supports them, validates them, or proves the Beluga
protocol satisfies them.

The headline §5 result `beluga_isBlockSynchronizer` (in
[`BlockSynchroniser/Beluga/Theorems.lean`](BlockSynchroniser/Beluga/Theorems.lean))
takes a single Prop-bundle `BelugaWithPullFairness` packaging the
paper's §2 + §4.2 + §4.3 partial-synchrony assumptions and concludes
that Beluga's network-aware trace satisfies all four
block-synchronizer properties — fully derived, with no `Eventual*`
axioms.

## Build

```bash
lake update
lake build
```

Requires Lean 4 toolchain `leanprover/lean4:v4.28.0` (pinned in
[`lean-toolchain`](lean-toolchain)). The `lake update` step pulls Mathlib
and Batteries; the `lake build` step uses Mathlib's cloud cache to avoid
recompiling Mathlib from scratch.

## Documentation

Pointers to the documents most likely to be useful — paper-facing first,
then code-facing.

### For the paper authors

| Document | What it is |
|---|---|
| [docs/round-01/mechanization-findings.md](docs/round-01/mechanization-findings.md) | Running log of paper-side observations from the formalization. Each finding (`F-1` through `F-13`) has severity, category, affected paper sections, headline issue, recommended action, and our address. Paper terminology only. |
| [docs/round-01/paper-additions-stage1.md](docs/round-01/paper-additions-stage1.md) | Stage-1 list of recommended paper edits — items whose Lean proofs are fully closed, in the order theorems appear. |
| [docs/round-01/paper-additions-stage2.md](docs/round-01/paper-additions-stage2.md) | Stage-2 follow-ups (paper-faithfulness commentary on §5, alternative proof sketches, recommended §4 changes). |
| [docs/round-01/Block_Sync_Project.pdf](docs/round-01/Block_Sync_Project.pdf) | The paper itself. |

### Project overview

| Document | What it is |
|---|---|
| [formalization.md](formalization.md) | The canonical paper→code map. Per-paper-section table mapping every paper definition / lemma / theorem to its Lean home and proof status, plus the `BlockInv → AcceptInv → CausallyClosed` refinement-chain narrative. |
| [changelogs/](changelogs/) | Per-stage timestamped changelogs. |

### Code map

The paper-facing layers live in:

- [`BlockSynchroniser/Beluga/Network.lean`](BlockSynchroniser/Beluga/Network.lean) —
  paper §4 protocol layer: `NetworkState`, `networkStep`,
  `networkStepWithPull`, the §4.2 push protocol, the §4.3 pull
  mechanism, the fairness derivation, and the named liveness
  primitives (`NetworkDeliveryWithPull`, `ActionSchedulingWithPull`,
  `BoundedRoundSpread_networkTraceWithPull`, `AcceptScheduling`,
  `PullRequestDelivery`, `PullResponseScheduling`,
  `NetworkInPoolDeliveryWithPull`).
- [`BlockSynchroniser/Beluga/Theorems.lean`](BlockSynchroniser/Beluga/Theorems.lean) —
  paper §5 layer: the `BelugaWithPullFairness` bundle, the §5 lemmas
  L1 and L2, the §5 theorems T1–T4 (with `Eventual*` discharged as
  derived theorems), and the corollary `beluga_isBlockSynchronizer`.

See [formalization.md](formalization.md#repository-layout) for the
full per-file breakdown.

## Project structure

```
block-sync-lean/
├── BlockSynchroniser/          # Library modules (per-concept files)
├── Main.lean                   # Executable driver
├── docs/                       # Paper-side findings, the paper, deep dives
├── changelogs/                 # Per-stage changelogs
├── formalization.md            # Overview & entry point
└── README.md                   # This file
```

## License

Apache License, Version 2.0 — see [LICENSE](LICENSE).
