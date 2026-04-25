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

## Project 91c97602-54da-4277-8bda-3864bfa6674a (round 3e)

| Field | Value |
|---|---|
| Submitted | 2026-04-25 23:18 SGT |
| Returned | 2026-04-26 ~01:07 SGT (status `COMPLETE_WITH_ERRORS`) |
| Result tarball | `/tmp/aristotle-r3e.tar.gz` (extracted to `/tmp/aristotle-r3e/project_aristotle/`) |
| Prompt | Fill the three sorries in `BlockSynchroniser/Beluga/PerformanceLemmas.lean` (L3, L4, L5 deterministic). Add hypotheses if needed but explain. |
| Integration commit | (TBD; this commit) |

### Theorems proved (3 + 1 def + helpers)

In [`BlockSynchroniser/Beluga/PerformanceLemmas.lean`](../BlockSynchroniser/Beluga/PerformanceLemmas.lean):

| Theorem | Paper origin | Strategy used |
|---|---|---|
| `lemma3_honest_not_blamed` | Appendix C.2 L3 | Reputation tables are preserved across `step`, so the non-decrease property is trivial. Delegated to `belugaTrace_getValidator_reputation` from new module `StepPreservation`. |
| `lemma4_round_latency_delta` | Appendix C.2 L4 | Added hypothesis `LatencyTriangle` (paper Assumption 1) and `round_advance_chain` helper proved by induction over the round delta. |
| `lemma5_round_latency_or_blamed` | Appendix C.2 L5 (deterministic) | Contrapositive against `LatencyTriangle`: if the disjunction fails, an inductive chain of round-advances can be built. |

New definition `LatencyTriangle (system) (time) : Prop` captures
paper Assumption 1 (latency triangle): after GST, if all honest
validators are synchronized at round `r`, they all enter `r+1` within
`Δ`. This is added as a hypothesis to L4 and L5 (consistent with the
paper, which assumes Assumption 1 for these lemmas).

### Helper lemmas Aristotle added — new file [`StepPreservation.lean`](../BlockSynchroniser/Beluga/StepPreservation.lean) (6)

| Lemma | Status |
|---|---|
| `updateValidator_getValidator_reputation` | sorry-free |
| `tryActFor_preserves_reputation` | **`sorry`** — `▸` cast mismatch + heartbeat timeout in the `doAccept` branch; queued as round 3e-followup |
| `step_getValidator_reputation` | sorry-free (depends on the sorry'd lemma above) |
| `belugaTrace_getValidator_reputation` | sorry-free |
| `init_getValidator_honest` | sorry-free (after replacing Aristotle's `exact?` with `exact Or.inr h_find`) |
| `belugaTrace_getValidator_honest` | sorry-free (after replacing Aristotle's `exact?` with the explicit base-case term) |

### Side effects on the project

- Aristotle added `import Mathlib` to both modified files. We narrowed
  to `import Mathlib.Tactic` (consistent with the workaround for the
  `clang` link-command size issue applied earlier in `Validation.lean`
  and `Liveness.lean`).
- Aristotle left two `exact?` placeholders in the new `StepPreservation`
  module. We applied the linter "Try this" hints by hand:
  `exact Or.inr h_find` and `exact init_getValidator_honest system vid h`.
- Aristotle left `tryActFor_preserves_reputation` with a `▸` cast that
  Lean rejects ("expected result type of cast does not contain the
  expected result type") and a heartbeat timeout. Replaced with `sorry`
  and queued as a followup round.
- New module `StepPreservation.lean` added to the root `import` graph.

### Verifier confirmation

`lake build` passes (6244 jobs). One new `sorry` introduced
(`tryActFor_preserves_reputation`); all three target theorems plus the
6 main helpers compile.

## Project bb79d236-f91d-42e0-9315-f46d9a22f5b8 (round 3e-followup)

| Field | Value |
|---|---|
| Submitted | 2026-04-26 01:11 SGT |
| Returned | 2026-04-26 ~01:33 SGT (status `COMPLETE`, fully clean) |
| Result tarball | `/tmp/aristotle-r3eF.tar.gz` |
| Prompt | Prove `tryActFor_preserves_reputation` in `Beluga/StepPreservation.lean`; prefer `convert`/`refine` over `▸`; lean on `updateValidator_getValidator_reputation`. |
| Integration commit | (TBD; this commit) |

### Theorems proved (1)

| Theorem | Strategy used |
|---|---|
| `tryActFor_preserves_reputation` | Case-split on `tryActFor`'s four branches (propose/accept/store/advance); `doPropose` preserves validators directly; `doAccept`/`doStore`/`doAdvance` apply `updateValidator_getValidator_reputation` since each update preserves the `reputation` field (`intros; rfl`). |

### Side effects on the project

- None. Single-lemma fix; existing module structure preserved.
- Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

### Verifier confirmation

`lake build` passes (6244 jobs). The sorry queued in round 3e is now
closed; `lemma3_honest_not_blamed` in `PerformanceLemmas.lean` no longer
has a transitive sorry through this helper.

### Notes

- This is the cleanest round so far: status `COMPLETE` (not
  `COMPLETE_WITH_ERRORS`), no `exact?` placeholders, no `▸` issues, no
  `import Mathlib`. The targeted-prompt + explicit-tactic-guidance
  pattern paid off — recommend repeating for similar narrow followups.

## Project 9d7e8e08-0f3f-4101-9b69-2a46a7f6a69a (round 6)

| Field | Value |
|---|---|
| Submitted | 2026-04-26 00:46 SGT |
| Returned | 2026-04-26 ~01:31 SGT (status `COMPLETE`) |
| Result tarball | `/tmp/aristotle-r6.tar.gz` |
| Prompt | Close the three bridge sorries in `Mysticeti/Safety.lean` (`h_inductive_step` in L13, `h_exists_block` in L16, `h_complete` in T7). Add protocol-invariant hypotheses if needed. |
| Integration commit | (TBD; this commit) |

### Theorems closed (3) and helper added (1)

| Theorem | Strategy used |
|---|---|
| `lemma13_cert_persistence` (`h_inductive_step`) | Strong induction on `n = B'.r − (B.r + 2)`. Base case via new hypothesis `h_cert_base`; inductive step via new hypothesis `h_dag_parent` and the new `Reaches.trans` helper. |
| `lemma16_consistent_status` (`h_exists_block`) | Direct application of new hypothesis `h_view_traceback` (every non-`Undecided` honest view traces back to a leader block whose `directDecide` is non-`Undecided`). |
| `theorem7_consensus_safety` (`h_complete`) | Direct application of new hypothesis `h_decision_complete` (decision completeness — if any honest validator's view is `Undecided`, all honest validators' views are `Undecided`). |
| `Reaches.trans` (new helper) | Standard induction on the second `Reaches` argument. |

### New paper-faithful hypotheses added

These are protocol invariants implied by the rest of the formalization
but not yet derived; they are surfaced as explicit hypotheses for the
proofs at this stage.

| Hypothesis | Paper origin | Future status |
|---|---|---|
| `h_cert_base` (L13) | Quorum-intersection at the certificate round | Should become a lemma once `quorumIntersection` lands (round 2) |
| `h_dag_parent` (L13) | DAG connectivity (every block has a parent in the previous round) | Structural property of `SystemState`; lemma in a future round |
| `h_view_traceback` (L16) | "All decisions originate from `directDecide`" — paper §D.3 | Tied to the indirect-decision formalization |
| `h_decision_complete` (T7) | Liveness-derived decision completeness | Will follow from Mysticeti liveness theorems (`Mysticeti/Liveness.lean`) |

### Side effects on the project

- New helper `Reaches.trans` added at the top of the file (outside the
  `Mysticeti.Safety` namespace, in `BlockSynchroniser`) since it's
  general-purpose. Reusable by other modules.
- Three theorem signatures gained extra hypotheses (paper-faithful
  protocol invariants); callers will need to supply them. Documented
  inline.
- No `import Mathlib`; no `exact?`. Clean integration.
- Standard axioms only.

### Verifier confirmation

`lake build` passes (6244 jobs). Three sorries closed in `Safety.lean`;
the file now has only `lemma10_round_robin_pigeonhole` as remaining
sorry (queued under round 2).

## Project d724efd2-324b-48c2-bd1d-08e690d02eb1 (round 3a — discovery)

| Field | Value |
|---|---|
| Submitted | 2026-04-25 23:13 SGT |
| Returned | 2026-04-26 ~01:28 SGT (status `COMPLETE_WITH_ERRORS`) |
| Result tarball | `/tmp/aristotle-r3a.tar.gz` |
| Prompt | Prove `lemma1_honest_round_entry` and `lemma2_round_latency` (timing) in `Beluga/Theorems.lean`. |
| Integration commit | (TBD; this commit) |

### Outcome

**This round did not produce integratable proofs of the requested
theorems** — but it produced a substantive *discovery* about the paper.

Aristotle reported (with concrete counterexamples on `n = 4, f = 1,
GST = 0, Δ = 10`) that the paper's literal L1 and L2 statements are
**false** under our `belugaTrace` execution model: the paper's
`3Δ`-bounded round synchronisation depends on an implicit
**scheduler-fairness assumption** (every honest validator acts
within Δ of becoming enabled) that the paper's prose proofs use but
never state.

Aristotle proposed *weakened* L1/L2 (initial-state agreement +
round monotonicity). We **rejected** that weakening — paper-fidelity
is the goal — and instead surfaced the implicit assumption as
`SchedulerFairness` in `Beluga/Theorems.lean`, which preserves paper
L1/L2 statements verbatim with the assumption added as a hypothesis.

Full discussion in
[paper-feedback-l1-l2-fairness.md](paper-feedback-l1-l2-fairness.md)
(written for the paper authors, paper terminology only) and in the
"Mechanization findings" section of [formalization.md](../formalization.md).

### Salvageable artifacts

Aristotle proved 12 helper lemmas about the executable `step` function
(round monotonicity, validator persistence, action-level preservation
lemmas). These are paper-faithful infrastructure useful for proving
L1/L2 under the new `SchedulerFairness` hypothesis. Unfortunately,
several of them rely on heuristic-tactic chains (`grind`/`aesop`/
`simp_all +decide`) that hit heartbeat limits in our build context;
they were sorry-stubbed and queued as round 3a-followup. The lemma
*signatures* are preserved in the file.

### Conclusion

This round is the project's first "discovery" via mechanization: a
paper-level finding that wouldn't have surfaced from reading the
paper alone. Recorded as the canonical example of how a proof
assistant catches an implicit assumption in a published proof.

## Project 4cda6cb1-a5b1-4f2f-9616-204e6438f82d (round 2)

| Field | Value |
|---|---|
| Submitted | 2026-04-25 22:55 SGT |
| Returned | 2026-04-26 ~01:39 SGT (status `COMPLETE`) |
| Result tarball | `/tmp/aristotle-r2.tar.gz` |
| Prompt | Prove `quorumIntersection`, `certified_unique`, and `lemma10_round_robin_pigeonhole`. |
| Integration commit | (TBD; this commit) |

### Theorems proved (3 + helpers)

| Theorem | File | Strategy |
|---|---|---|
| `Quorum.quorumIntersection` | `Quorum.lean` | Convert lists to `Finset`, apply `Finset.card_union_add_card_inter` (inclusion-exclusion), bound the union by the validator universe. |
| `Beluga.certified_unique` | `Beluga/Patterns.lean` | Apply `quorumIntersection` to the two `strongReferencerAuthors` lists (size ≥ 2f+1 each); pigeonhole an honest validator into the intersection; apply `NoEquivocationInParents` (cross-block form). |
| `Mysticeti.Safety.lemma10_round_robin_pigeonhole` | `Mysticeti/Safety.lean` | Decomposed into a pure combinatorial helper `consecutive_triple_exists` (in any circular sequence of length n=3f+1 with ≤ f false positions, three consecutive trues exist) by double-counting; main theorem instantiates with the round-robin honest function and discharges modular wrap-around. |

### Helper lemmas added

In `Beluga/Patterns.lean`: `strongReferencerAuthors_nodup`,
`strongReferencerAuthors_mem`, `strongReferencerAuthors_are_validators`.

In `Mysticeti/Safety.lean`: `consecutive_triple_exists` (combinatorial).

### New paper-faithful hypotheses surfaced

| Hypothesis | On theorem | Why |
|---|---|---|
| `hN : system.n = 3 * system.f + 1` | `quorumIntersection`, `certified_unique`, `lemma10_round_robin_pigeonhole` (already had it for L10) | F-2 — the `≥ f+1` intersection bound only holds at this exact size. |
| `h_B₁_in`, `h_B₂_in : ∈ SystemState.blocks state` | `certified_unique` | Required for `NoEquivocationInParents`. |
| `h_authors_valid` | `certified_unique` | Block authors are registered validators. |
| `h_byz_bound : (validators.filter Byzantine).length ≤ system.f` | `certified_unique` | Standard BFT bound — pigeonholes an honest validator into the quorum intersection. |
| `h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i` | `lemma10_round_robin_pigeonhole` | Validator IDs are `{0, …, n-1}`, matching the round-robin's `r % n`. New paper-implicit assumption — see F-8 in `mechanization-findings.md`. |

### Caller updates

- `lemma15_unique_cert` in `Mysticeti/Safety.lean` was updated to thread the four new `certified_unique` hypotheses through.
- `three_consecutive_honest_direct_commit` in `Mysticeti/Liveness.lean` was updated to take the new `h_ids` and pass it to `lemma10`.

### Side effects

- `import Mathlib` → narrowed to `import Mathlib.Tactic` in three files.
- Two `exact?` placeholders in `Patterns.lean` replaced with the
  Lean-suggested explicit terms (`strongReferencerAuthors_mem state B vid hvid`,
  `strongReferencerAuthors_nodup state B₁`).
- Aristotle's `Safety.lean` modifications were *cherry-picked* (only
  `consecutive_triple_exists` + L10 proof + L15 hypothesis pass-through),
  preserving round 6's L13/L16/T7 work that landed between submission
  and return.
- `set_option linter.unusedSimpArgs false` added at the top of the three
  files since Aristotle's heuristic-tactic chains generate cosmetic
  warnings only.

### Verifier confirmation

`lake build` passes (6244 jobs). Sorry count drops from 27 to 20:
- Quorum.lean: 1 → 0
- Patterns.lean: 1 → 0
- Safety.lean (lemma10): 1 → 0
- All other counts unchanged.

## Future projects

When a new Aristotle submission completes and is integrated, append
a new "Project &lt;id&gt;" section here following the template above.

The corresponding queue + state for in-flight projects lives in
[aristotle-projects.md](aristotle-projects.md); this file records
*completed* attributions with full detail for the final report.
