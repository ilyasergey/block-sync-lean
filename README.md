# BlockSynchroniser

A Lean 4 formalization of *Beluga: Block Synchronization for BFT Consensus
Protocols*.

## Goals

A formal model of a block synchronizer for BFT consensus: validators
collectively build a structured, ever-growing set of blocks while tolerating
up to `f` Byzantine validators out of `n ≥ 3f + 1`. The four properties of
Definition 1 (Round-Progression, Round-Termination, Block availability,
Causal availability) are the load-bearing definitions. The formalization:

- defines the §4 Beluga protocol semantics (admission control,
  reputation, push/pull, network model);
- proves the §5 main theorems (T1–T4) — Beluga satisfies all four
  block-synchronizer properties;
- proves the Appendix C deterministic performance bounds (L3, L4,
  L5);
- proves the Appendix D Mysticeti-Beluga consensus theorems
  (safety T7 and liveness T6, plus the supporting lemmas L7–L16).

## Build

```bash
lake update
lake build
```

Requires the Lean 4 toolchain `leanprover/lean4:v4.28.0` (pinned in
[`lean-toolchain`](lean-toolchain)).

## Run

```bash
lake exe blocksynchroniser
```

Drives a small executable trace and prints the operation log.

## Overview

See [formalization.md](formalization.md) for the paper → code map and
per-theorem proof status.

## License

Apache License, Version 2.0 — see [LICENSE](LICENSE).
