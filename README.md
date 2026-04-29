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
- proves the Appendix C deterministic performance bounds (L3, L4, L5);
- proves the Appendix D Mysticeti-Beluga consensus theorems (safety
  T7 and liveness T6, plus the supporting lemmas L7–L16).

**Not formalized.** The probabilistic / expected-value claims:
random-pull complexity bound (§4.3), expected-latency bounds (§C
Lemmas 6, 7 and Theorem 5), and the expected-latency disjunct of
Lemma 5. The recursive descent of the §D.1.1 indirect-decision rule
is also not mechanized — Lemma 11 is formalized in its existential
form, which is what Theorem 6's proof actually consumes.

## Overview

See [formalization.md](formalization.md) for the paper → code map and
per-theorem proof status.

## Installing Lean

This project requires Lean 4 toolchain `leanprover/lean4:v4.28.0` (pinned
in [`lean-toolchain`](lean-toolchain)). Use [`elan`](https://github.com/leanprover/elan),
the Lean version manager — it picks up the pinned toolchain automatically:

```bash
# Linux / macOS:
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Windows: see https://github.com/leanprover/elan#windows
```

After installation, restart your shell or `source ~/.profile` so `lean`,
`lake`, and `elan` are on your PATH.

## Build

```bash
lake update
lake build
```

The first `lake update` fetches Mathlib and Batteries; the first build
uses Mathlib's cloud cache to avoid recompiling Mathlib from scratch.

## Run

```bash
lake exe blocksynchroniser <command> [steps]
```

Drives the executable Beluga `step` function on a chosen system and
prints a state summary (operation counts, block-pool size, round-0/1
proposers, per-validator current round). The schedule is round-robin
honest: at each step the scheduler scans validators in id order and
applies the first available action (priority: propose → accept →
store → advance).

| Command         | What it does                                                        |
|-----------------|---------------------------------------------------------------------|
| `small [n]`     | Run the 4-validator (`f=1`) all-honest system for `n` steps (default 20). |
| `medium [n]`    | Run the 7-validator (`f=2`) all-honest system.                      |
| `large [n]`     | Run the 13-validator (`f=4`) all-honest system.                     |
| `log [n]`       | Run `small n` and additionally print the operation log.             |
| `compare [n]`   | Run `small`, `medium`, and `large` for `n` steps; print summaries side by side. |
| `help`          | Show usage.                                                         |

If no command is given, runs `small 20` and prints the operation log.

```bash
# Examples:
lake exe blocksynchroniser small 60
lake exe blocksynchroniser compare 100
lake exe blocksynchroniser log 12
```

## License

Apache License, Version 2.0 — see [LICENSE](LICENSE).

## Acknowledgements

The Lean proofs in this project were produced with the help of Anthropic's
Claude Opus 4.7 and Harmonic's [Aristotle](https://aristotle.harmonic.fun/).
