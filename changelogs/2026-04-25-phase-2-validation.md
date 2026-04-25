# 2026-04-25 — Phase 2: Validation (non-vacuity)

Stand up `BlockSynchroniser/Validation.lean` — the (B) realizability lemmas
and (C) anti-witnesses, and state-but-defer the (A) goldenTrace satisfaction
theorems for delegation to Aristotle.

Also: lock in "Phase 4 ships an executable step + refinement lemma" in
[docs/formalization-plan.md](../docs/formalization-plan.md). No Phase-2
runnability shortcut.

## What's new

### Hand-proved (no `sorry`)

| Lemma | Statement |
|---|---|
| `realizable_propose` | Some trace at some step has *some* validator proposing. |
| `realizable_accept` | Some trace at some step has *some* validator accepting. |
| `realizable_store` | Some trace at some step has *some* validator storing. |
| `not_roundProgression_emptyTrace` | The empty trace does *not* satisfy `RoundProgression goldenSystem`. |
| `not_roundTermination_emptyTrace` | The empty trace does *not* satisfy `RoundTermination goldenSystem`. |

These five close two of the three layers of non-vacuity defense:
- **(B)** the antecedents `HasProposed`/`HasAccepted`/`HasStored` are reachable
  somewhere — properties aren't trivially true because their hypotheses can
  never fire.
- **(C)** the empty trace fails at least Round-Progression and Round-Termination
  — the properties can't be passed by a no-op trace.

### Stated and deferred (with `sorry` + `PROVIDED SOLUTION` sketches)

| Theorem | Plan |
|---|---|
| `golden_roundProgression` | Witness `k = 36*r + 4`. Aristotle. |
| `golden_roundTermination` | Witness `k = 36*(r+1)`; uses `authorOfDigest`. Aristotle. |
| `golden_blockAvailability` | Decompose `d = r*4 + i`; locate the corresponding store at step `k + 36`. Aristotle. |
| `golden_causalAvailability` | Induction on `r' ≤ r` over the parent chain. Aristotle. |

Each sorry has a `PROVIDED SOLUTION` block in its docstring with the proof
sketch — that's the prompt-style guidance Aristotle uses (see
[docs/aristotle-workflow.md](../docs/aristotle-workflow.md)).

The convenience corollary `goldenTrace_isBlockSynchronizer` is a one-line
conjunction of the four sorried theorems; it gates on them but doesn't add a
new sorry of its own.

### Infrastructure

- `BlockSynchroniser/Operations.lean`: `ValidatorOperation` now also derives
  `DecidableEq` (used by realizability proofs).
- `goldenSystem` constructor with `decide`-discharged invariants.
- `gBlock`, `gBlocksThrough`, `gRoundOps`, `gOpsThrough`: per-round periodic
  structure (4 propose + 16 accept + 16 store = 36 ops per round).
- `goldenStateAt`, `goldenTrace`: the periodic trace.

## Aristotle work this stage

None yet. Four theorems are queued for delegation; the prompt and project-dir
recipe is ready in [docs/aristotle-workflow.md](../docs/aristotle-workflow.md).
First submission will happen as a separate sub-stage so we can review
Aristotle's output cleanly.

## Build

`lake build` clean — 26 jobs, 5 expected `sorry` warnings:

- `Quorum.lean :: quorumIntersection` (Phase 1, deferred)
- `Validation.lean :: golden_{roundProgression, roundTermination, blockAvailability, causalAvailability}` (this stage, deferred)

## Plan changes

`docs/formalization-plan.md` Phase 4 section now explicitly commits to:

> A computable `step : … → BelugaState` … used to run the protocol (`#eval`,
> `Main.lean` driver) and a refinement lemma showing every transition `step`
> produces satisfies `HonestStep`.

No Phase-2 runnability shortcut.

## Status delta

| Category | Before | After |
|---|---|---|
| Validation | 0 done / 5 planned | 7 done / 4 deferred |
| Total ✅ | 7 | 14 |
| Total ◐ | 3 | 7 |
| Total ☐ | 30 | 23 |

## Next stage

Either:
- **Sub-stage 2.5**: Submit the four `golden_*` theorems to Aristotle. Review
  the diff, apply, verify, document attribution.
- **Phase 3**: Beluga block extensions and patterns (`BlockExt`, `Patterns`,
  including the uniqueness-of-certified lemma).

Awaiting direction.
