# Aristotle attribution log

Audit trail of theorems / lemmas in this formalization that were proved
by Aristotle (Harmonic). For the operational protocol see
[aristotle-workflow.md](aristotle-workflow.md). For per-project state
see [aristotle-projects.md](aristotle-projects.md).

This file is the source of truth for **the final report's attribution
section**. Each entry records: project ID, target file, theorem(s)
proved, helper lemmas added, what we asked for, what came back, and
the integration commit.

## Project be7c0245-cdb9-4cce-9c4a-fffecfd1a69c

| Field | Value |
|---|---|
| Submitted | 2026-04-25 21:25:15 SGT |
| Returned | 2026-04-25 ~22:50 SGT (status `COMPLETE_WITH_ERRORS` per Aristotle, but all four target sorries closed cleanly) |
| Project tarball | `/tmp/aristotle-validation-20260425-212515.tar.gz` |
| Result tarball  | `/tmp/aristotle-out-validation/project_aristotle/` |
| Prompt | "Fill in the sorries in BlockSynchroniser/Validation.lean. Each theorem has a PROVIDED SOLUTION sketch in its docstring with the proof strategy. Do not modify any other files." |
| Integration commit | `009bb10` |

### Theorems proved (4)

All four `golden_*` theorems in
[`BlockSynchroniser/Validation.lean`](../BlockSynchroniser/Validation.lean):

| Theorem | Paper origin | Strategy used |
|---|---|---|
| `golden_roundProgression` | Validation of paper §2.1 Definition 1.1 | At step `36*(r+1)` all four validators have proposed for round `r`; deduplicated proposers list = `[0,1,2,3]`, length 4 ≥ `2f+1 = 3`. |
| `golden_roundTermination` | Validation of Definition 1.2 | At step `36*(r+1)`, each honest validator has accepted blocks from all four round-`r` proposers; via `authorOfDigest` the deduplicated authors list = `[0,1,2,3]`. |
| `golden_blockAvailability` | Validation of Definition 1.3 | For any accepted digest, locate the corresponding `block_store` operation later in the periodic schedule. |
| `golden_causalAvailability` | Validation of Definition 1.4 | Induction on `Reaches`; show all causal ancestors of an accepted block are also accepted. |

### Helper lemmas Aristotle added (11)

All in [`Validation.lean`](../BlockSynchroniser/Validation.lean), each
marked with `-- proof: aristotle (project be7c0245)`:

- `gRoundOps_length` — each round's operation list has length 36.
- `gOpsThrough_length` — operations through round `R` have length `36*(R+1)`.
- `gOpsThrough_succ` — splitting operations by round.
- `gOpsThrough_take_full` — taking the full prefix.
- `goldenTrace_ops_at_full_round` — ops at step `36*(r+1)` equal `gOpsThrough r`.
- `gRoundOps_propose_mem`, `gRoundOps_accept_mem`, `gRoundOps_store_mem` — membership lemmas for each operation type.
- `gRoundOps_mem_gOpsThrough` — lifting round-level membership to cumulative ops.
- `propose_mem_gOpsThrough`, `accept_mem_gOpsThrough`, `store_mem_gOpsThrough` — convenience wrappers.
- `isHonest_goldenSystem_iff` — honest validators are exactly `{0,1,2,3}` in `goldenSystem`.

### Side effects on the project

- Aristotle added `import Mathlib` to `Validation.lean`. We narrowed
  this to `import Mathlib.Tactic` + a few `Mathlib.Data.List.*`
  imports to keep the executable link command small enough for
  `clang`. Aristotle's proofs work unchanged with the narrower
  imports.
- No other files were modified. ✓
- All proofs use only standard axioms (`propext`, `Classical.choice`,
  `Quot.sound`) — confirmed by Aristotle's summary.

### Verifier confirmation

`lake build` passes cleanly with the integrated proofs (6240 jobs).

### Notes on the `COMPLETE_WITH_ERRORS` status

Aristotle returned `COMPLETE_WITH_ERRORS` despite all four target
theorems being proved. Possible cause: a transient internal verifier
issue on Aristotle's side that did not invalidate the output. Result
is sound — `lake build` succeeds, and Aristotle's `ARISTOTLE_SUMMARY.md`
confirms all four theorems proved.

## Future projects

When a new Aristotle submission completes and is integrated, append
a new "Project &lt;id&gt;" section here following the template above.

The corresponding queue + state for in-flight projects lives in
[aristotle-projects.md](aristotle-projects.md); this file records
*completed* attributions with full detail for the final report.
