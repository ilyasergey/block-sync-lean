# Aristotle attribution log

Audit trail of theorems / lemmas in this formalization that were proved
by Aristotle (Harmonic). For the operational protocol see
[aristotle-workflow.md](aristotle-workflow.md). For per-project state
see [aristotle-projects.md](aristotle-projects.md).

This file is the source of truth for **the final report's attribution
section**. Each entry records: project ID, target file, theorem(s)
proved, helper lemmas added, what we asked for, what came back, and
the integration commit.

## Project 116385ce-5fc6-4f0c-8083-a2ed4c66d514 (round 3f)

| Field | Value |
|---|---|
| Submitted | 2026-04-25 23:14 SGT |
| Returned | 2026-04-26 ~00:24 SGT (status `COMPLETE_WITH_ERRORS`) |
| Result tarball | (pre-session) |
| Prompt | Prove `step_refines_HonestStep` in `Beluga/Protocol.lean` (initial framing). |
| Integration commit | `d96ce2e` |

### What landed (preserved through this session)

This was the *first* round at `step_refines_HonestStep`. It returned
a structural proof skeleton with 5 inline gaps. The skeleton was
later replaced wholesale by round 4 (`a8889396`), but three helper
lemmas Aristotle introduced **survived** and are still load-bearing:

- `hasAcceptedDigest_false_imp` (`hasAcceptedDigest false ⇒ ¬HasAccepted`)
- `hasAcceptedDigest_true_imp` (`hasAcceptedDigest true ⇒ HasAccepted`)
- `not_honest_imp_byzantine` (registered + ¬honest ⇒ Byzantine)

These three are still tagged `-- proof: aristotle (project 116385ce)`
in `Beluga/Protocol.lean` (around line 315).

### Notes

This round is the precursor to round 4 (`a8889396`); the bulk of
its proof body was superseded, but the small infrastructure lemmas
remain, so a permanent attribution entry is warranted.

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

## Project a8889396-b34e-40f2-b10b-388f960c088e (round 4)

| Field | Value |
|---|---|
| Submitted | 2026-04-26 00:46 SGT |
| Returned | 2026-04-26 ~02:20 SGT (status `COMPLETE_WITH_ERRORS`) |
| Result tarball | `/tmp/aristotle-r4.tar.gz` |
| Prompt | Prove `step_refines_HonestStep` in `Beluga/Protocol.lean` under the paper-consistent `HonestAccept`/`HonestStore` preconditions and the new `BelugaState.WellFormed` hypothesis. |
| Integration commit | (TBD; this commit) |

### Theorems closed (1 main + 6 sorry-free helpers)

| Theorem | Strategy |
|---|---|
| `step_refines_HonestStep` (main) | By contradiction. Unfold `step`; case-split on `findSome?`. No-op case via `honestStep_of_no_op`; otherwise extract `(vid, bv)` via `Lib.findSome_witness` and dispatch to `tryActFor_honestStep`. |
| `tryActFor_honestStep` | Unfold `tryActFor`; case-analyze the four branches (propose/accept/store/advance); dispatch to per-action helper. |
| `honestStep_of_no_op` | `ByzantineStep` with empty op list — vacuously satisfies the constraint. |
| `honestStep_of_advance` | `doAdvance` emits no operations, so `ByzantineStep` with `[]` works regardless of honesty. |
| `honestStep_of_propose` | Case-split on honest/Byzantine. Honest: `HonestPropose` witness. Byzantine: `ByzantineStep` + `not_honest_imp_byzantine`. |
| `honestStep_of_accept` | Honest: `HonestAccept` witness; uses `List.find?_some`, `hasAcceptedDigest_false_imp`, `hasAcceptedDigest_true_imp`. Byzantine: same pattern as propose. |
| `honestStep_of_store` | Honest: `HonestStore` witness; delegates causal-history precondition to `causal_history_of_find_none`. Byzantine: same pattern. |

### Remaining sorry (1)

| Lemma | Why deferred |
|---|---|
| `causal_history_of_find_none` | Trace-level invariant: `parentsAccepted` is checked at each accept step, so ancestors are accepted bottom-up — but proving it requires reasoning about the accumulation of accepted digests across the entire trace, not single-step state. Deferred to a dedicated trace-invariant module (future work). |

### Side effects

- All seven new helpers are `private` in the `BlockSynchroniser` namespace.
- No `import Mathlib`. No `exact?` placeholders. Proof body is mostly
  structural with localised `aesop`/`grind`/`simp_all` calls.
- Reused three previously-introduced helpers from project `116385ce`
  (`hasAcceptedDigest_false_imp`, `hasAcceptedDigest_true_imp`,
  `not_honest_imp_byzantine`).

### Verifier confirmation

`lake build` passes (6244 jobs). One new sorry (`causal_history_of_find_none`);
`step_refines_HonestStep` itself is sorry-free at the top level but has
a transitive sorry through this helper.

## Project d32908b4-d387-4d77-ac37-87e03a6f6699 (round 5)

| Field | Value |
|---|---|
| Submitted | 2026-04-26 00:46 SGT |
| Returned | 2026-04-26 ~05:30 SGT (status `COMPLETE_WITH_ERRORS`) |
| Result tarball | `/tmp/aristotle-r5.tar.gz` |
| Prompt | Fill the 11 sorry'd helper lemmas in `Mysticeti/Liveness.lean` (created by round 3d under lemma8/9/11/12/T6). |
| Integration commit | (TBD; this commit) |

### What landed

Each of the 11 helper lemmas now has a *structured proof* that follows
the paper's argument (§D.2). Compositional steps (e.g.,
`honest_references_leader_within_4delta` composes
`leader_block_disseminated_within_delta` + `honest_round_entry_within_3delta`)
are spelled out; protocol-invariant atomic facts (step semantics, BFT
bounds, parent selection, ImPoA availability) are sorry'd as inline
sub-steps with paper-citation comments.

| Helper | Sub-sorries | Notes |
|---|---|---|
| `honest_round_entry_within_3delta` | 3 | Paper Lemma 1 applied to Beluga; each Δ-step is a sorry'd protocol invariant |
| `leader_block_disseminated_within_delta` | 1 | Honest leader's `doPropose` + `PartiallySynchronous` Δ |
| `honest_references_leader_within_4delta` | 1 | Composes the two above + parent-selection invariant |
| `lemma8_leader_referenced` | 0 | Fully via composition |
| `honest_validators_certify_leader` | 1 | Lemma 9 dependency |
| `lemma9_honest_certificate` | 0 | Composition |
| `three_consecutive_honest_direct_commit` | 1 | Calls `lemma10_round_robin_pigeonhole` + `honest_validators_certify_leader` |
| `backward_induction_decides_earlier_rounds` | 1 | Indirect-decision rule |
| `eventual_decision_core` | 2 (hN, hHonest as `have`) | Top-level composition; the BFT-bound `have`s are sorry'd as separate items |
| `lemma11_eventual_decision` | 0 | Composition |
| `at_least_f_plus_one_honest_referencers` | 1 | Honest/Byzantine partition by `List.length_eq_length_filter_add`; only the Byz≤f bound is sorry'd |
| `honest_blocks_eventually_received` | 1 | ImPoA pull / availability |
| `lemma12_referenced_accepted` | 0 | Composition |
| `committed_leader_has_2f_plus_1_refs` | 0 | (was already proved; preserved) |
| `honest_validator_eventually_accepts` | 1 | Block-accept derivation |
| `accepted_implies_in_order` | 1 | TransactionOrder axiom |
| `theorem6_consensus_liveness` | 0 | Composition |

Total: 14 inline sub-sorries remain (down from 11 bare sorries — the
helpers' bodies are now real proofs, just bottoming out in the
named protocol invariants).

### Newly proved auxiliaries

- `mem_of_mem_eraseDups` (sorry-free)
- `belugaTrace_blocks_monotone` (sorry-free)

### Side effects

- One caller signature update needed: `three_consecutive_honest_direct_commit`
  now takes `h_ids` (the F-8 contiguous-IDs hypothesis) and threads it to
  `lemma10_round_robin_pigeonhole`. Aristotle's tarball pre-dates round 2's
  `h_ids` addition; we fixed up the caller during integration.
- Top-of-file "Status:" prose stripped (per project convention).

### Verifier confirmation

`lake build` passes (6246 jobs). Sorry count: increases by ~13 net
(structured proofs surface previously-buried atomic gaps), but each
new sorry is a *named* protocol invariant rather than an opaque body
sorry. Per CLAUDE.md the structural decomposition is itself worth
committing.

## Project 9f17cf80-caba-4369-90b2-0a99a175e394 (admission-invariant round)

| Field | Value |
|---|---|
| Submitted | 2026-04-26 03:00 SGT |
| Returned | 2026-04-26 ~07:30 SGT (status `COMPLETE_WITH_ERRORS`) |
| Result tarball | `/tmp/aristotle-radm.tar.gz` |
| Prompt | Prove `belugaTrace_admissionWellFormed` (trace invariant) + the revised `lemma13_cert_persistence` (paper §D.3 argument with quorum-intersection derived inside, not assumed). |
| Integration commit | (TBD; this commit) |

### Theorems closed

| Theorem | Strategy |
|---|---|
| `belugaTrace_admissionWellFormed` | Defined a compound `TraceInv` carrying *four* simultaneous properties: `AdmissionWellFormed`, every `block_propose` op has its block in state, validators-IDs match the system, and validators at round r > 0 satisfy `allProposedFor (r-1)`. Proved `TraceInv` at init (vacuously), preserved by each `tryActFor` branch, and projected to `AdmissionWellFormed`. The hardest case is `doPropose` at round r > 0: the compound invariant supplies `allProposedFor (r-1)`, which then yields ≥ n distinct-author blocks at round r-1 — the parent witness. |
| `lemma13_cert_persistence` | Strong induction on `B'.r - (B.r + 2)`. Base case via `h_admission` + `Quorum.quorumIntersection` + `exists_honest_in_shared` (new helper) + `h_honest_unique` (new hypothesis: honest validator authors at most one block per (author, round) — standard BFT property). Inductive step via `h_admission` + IH + `Reaches.trans`. |

### New auxiliaries / hypotheses

- **New auxiliary `exists_honest_in_shared`**: pigeonhole — in a Nodup
  list of ≥ f+1 registered validators, at least one is honest given
  ≤ f Byzantine validators. Proved sorry-free.
- **New hypothesis on L13: `h_honest_unique`**: honest validators
  produce at most one block per `(author, round)` pair. This is
  standard BFT (follows from digital signatures); needed to identify
  the shared honest validator's parent block with their certificate
  block in the base case.
- **`set_option maxHeartbeats 800000`** at top of
  `AdmissionInvariant.lean`: Aristotle's `TraceInv` preservation
  proofs are deeply nested case-splits; the heartbeat bump is
  necessary for them to typecheck.

### Side effects

- `AdmissionInvariant.lean`: ~6 helper lemmas added (init,
  `hasProposedFor_append`, `allProposedFor_append`,
  `allProposedFor_of_same_ops`, `updateValidator_map_fst`,
  `admission_of_same_blocks`, `admission_of_cons_blocks`,
  `allProposedFor_gives_blocks`). All sorry-free.
- `Safety.lean`: `lemma13_cert_persistence`'s body filled; signature
  gained `h_honest_unique` and dropped the dead old hypothesis name
  references (signature otherwise as restructured).
- `set_option linter.unusedSimpArgs false` already at top of Safety
  (from earlier rounds); kept.
- No `import Mathlib`; no `exact?`; standard axioms only.

### Verifier confirmation

`lake build` passes (6246 jobs). Both target files are now sorry-free.
Sorry delta: −2 (the two we submitted to close); no new sorries added.

### Notes

- This round closes finding **F-5 (item 1)** entirely — the
  DAG-admission well-formedness invariant is now a *theorem* about
  `belugaTrace`, not a hypothesis. L13 specialised to `belugaTrace`
  no longer surfaces it as a side condition.
- Demonstrates the value of trace-invariant decomposition: the
  compound `TraceInv` carrier was the right framing for both the
  trace invariant and L13's quorum-intersection step.

## Project b544affb-b9a9-4f8c-965f-2a31051ef75f (theorems-helpers round)

| Field | Value |
|---|---|
| Submitted | 2026-04-26 09:05 SGT |
| Returned | 2026-04-26 ~10:25 SGT (status `COMPLETE`, fully clean) |
| Result tarball | `/tmp/aristotle-rh.tar.gz` |
| Prompt | Prove the two helper-stubs `step_preserves_validator_ids` and `step_round_monotone` in `Beluga/Theorems.lean`. |
| Integration commit | (TBD; this commit) |

### Theorems closed (2 + 1 auxiliary)

| Theorem | Strategy |
|---|---|
| `step_preserves_validator_ids` | Unfold `step`, case-split on `findSome?` and `tryActFor`'s four branches; structural analysis of `updateValidator`/`BelugaState.getValidator` plus the new helper `updateValidator_none`. |
| `step_round_monotone` | Unfold `step`, case-split on `findSome?` and `tryActFor` branches; reuse `doPropose_getValidator`, `doAccept_round`, `doStore_round`, `doAdvance_round` — each shows the corresponding action preserves or increments `currentRound`. |
| `updateValidator_none` (new aux.) | `updateValidator` preserves `getValidator vid = none`. |

### Side effects

- `set_option maxHeartbeats 800000 in` scoped per-lemma above the two
  targets (suggested in the prompt; needed for the deep `tryActFor`
  case analysis to typecheck).
- No `import Mathlib`. No `exact?`. Standard axioms only.

### Verifier confirmation

`lake build` passes (6246 jobs). The two previous sorry-stubs in
`Theorems.lean` are now closed; only the 6 main theorems (L1, L2,
T1–T4) remain pending in that file (queued in the next round).

### Notes

- This was the *focused replacement* for the canceled `58873be7`
  round (which had stalled at ~13% for 7+ hours with an 8-target
  scope). Tighter scope → 80 min completion vs. unbounded stall.
  Recommend this scope discipline as the default for trace/inductive
  helpers going forward.

## Project 3f6cf619-5a7f-4142-9114-c46caafa025f (round 4-followup)

| Field | Value |
|---|---|
| Submitted | 2026-04-26 02:30 SGT |
| Returned | 2026-04-26 ~11:10 SGT (status `COMPLETE`, fully clean) |
| Result tarball | `/tmp/aristotle-rch.tar.gz` |
| Prompt | Replace the `sorry` in `causal_history_of_find_none` with a real proof; suggested CausallyClosed carrier + monotonicity lemmas. |
| Integration commit | (TBD; this commit) |

### What landed — three-stage trace invariant

The single-state form of `causal_history_of_find_none` is unprovable;
Aristotle restructured around a three-stage trace invariant:

| Stage | Invariant | Captures |
|---|---|---|
| 1 | `BlockInv` | Every block has canonical digest `B.d = digest system B.r B.author`; corresponding `block_propose` op in log; uniqueness per `(validator, round)` pair; bounded author IDs. Together → no-duplicate-digests. |
| 2 | `AcceptInv` | (a) accepted digest ⇒ all parent digests accepted (`acceptedParents`); (b) accepted digest ⇒ corresponding block in pool (`acceptedBlockExists`). Hardest case: `doAccept` (uses no-duplicate-digests so the parent check covers all blocks). |
| 3 | `CausallyClosed` | Derived from `AcceptInv` by induction on `Reaches`: at each parent step the intermediate block is in the pool and accepted, so its parent digests are accepted by `acceptedParents`. |

Plus `causallyClosed_trace`: `CausallyClosed` holds at every trace step.

### Signature changes

To thread the trace ancestry through:

- `causal_history_of_find_none`: now takes `system : BlockSynchroniserSystem`, `hids : ValidIds system`, `hTrace : ∃ k, s = belugaTrace system k`. The original `hfindAccNone` is retained but unused (subsumed by the invariant).
- `honestStep_of_store`, `tryActFor_honestStep`, `step_refines_HonestStep`: gained `hids` and `hTrace` parameters (propagation only).
- `belugaTrace` was moved earlier in the file so the invariant section can reference it; `hasAcceptedDigest_true_imp` and `hasAcceptedDigest_false_imp` likewise.

### New definitions

| Definition | Role |
|---|---|
| `ValidIds system` | All validator IDs `< system.n + 1` (ensures `digest` injectivity). |
| `CausallyClosed s vid` | Target: accepted blocks have all causal ancestors accepted. |
| `BlockInv` / `AcceptInv` | Per-stage trace invariants with full per-action preservation lemmas. |
| `digest_injective`, `noDupDigests_of_blockInv`, `wellFormed_init`/`_step`/`_trace`, `HasAccepted` per-action iff-lemmas, monotonicity for each `do*` action | Supporting infrastructure (~15 lemmas) |

### Side effects

- No `import Mathlib`. No `exact?`. Standard axioms only.
- File grew from ~565 to ~837 lines (mostly new invariant infrastructure).
- The Status: bookkeeping at the top of Protocol.lean had to be re-stripped (Aristotle's tarball pre-dated our cleanup).

### Verifier confirmation

`lake build` passes (6246 jobs). `Beluga/Protocol.lean` is now
**0 sorries** (was 1: `causal_history_of_find_none`). `step_refines_HonestStep` is now fully transitively closed (no
remaining trace-invariant sorry).

### Notes

- This was a slow round: ~8h45m end-to-end. Trace-invariant proofs
  require Aristotle to invent the right inductive carrier (here:
  the 3-stage `BlockInv`/`AcceptInv`/`CausallyClosed` hierarchy);
  unsurprising that this takes longer than tactical-wall rounds.
- The 3-stage decomposition mirrors what we recommended for the
  `belugaTrace_admissionWellFormed` round (compound `TraceInv`
  carrier). Two-for-two now: when trace invariants are needed,
  Aristotle handles them well given enough time.

## Project 4f618efb-... (beluga-§5-bundle round, partial integration)

**Submitted.** 2026-04-26.
**Result.** `COMPLETE_WITH_ERRORS`. Aristotle returned a bundle proof
that "trivialised" by lifting four of the five conjuncts to
hypotheses (`h_round_sync = L1`, `h_store_liveness = T1`,
`h_propose_complete = T3`, `h_accept_complete = T4` — each hypothesis
literally equal to the conclusion it was supposed to prove). Only
the fifth conjunct (`honest_round_advance`, paper L2) was derived
non-trivially from a strengthened *lockstep* fairness assumption
(`h_lockstep`). Aristotle also produced 5 sorry-free helper lemmas
about the trace's round structure — these are genuinely useful
infrastructure independent of the bundle.

### Selectively integrated (5 helper lemmas + L2 inline derivation)

1. `doAdvance_round_at_most_one` — `doAdvance` increments the target
   round by at most 1 (case-split on `vid = vid'`).
2. `step_round_at_most_one` — `step` increases any validator's
   `currentRound` by at most 1 (case analysis on `tryActFor`'s four
   branches; mirrors `step_round_monotone`).
3. `honest_validator_persistent_trace` — honest validators are
   present at every trace step (Nat induction over
   `getValidator_persistent`).
4. `round_monotone_trace` — round monotonicity across arbitrary
   `k₁ ≤ k₂` (induction on `Nat.le`).
5. `round_intermediate_value` — **intermediate-value theorem for
   validator rounds**: if a validator's round is `≤ r` at `k₁` and
   `≥ r` at `k₂`, then there is some `k ∈ [k₁, k₂]` where the round
   is *exactly* `r`. Direct consequence of `step_round_at_most_one`.

These five lemmas land sorry-free in `Beluga/Theorems.lean`, marked
`-- proof: aristotle (project 4f618efb)`.

### Inline L2 derivation (in our `belugaTrace_satisfies_post_gst_liveness`)

Using the strengthened lockstep `SchedulerFairness` (which now
absorbs `h_lockstep` — see F-1a), L2's conclusion is derived from:
- `SchedulerFairness` to get a step `k'` with `bv'.currentRound ≥ r + 1`,
- `round_intermediate_value` to extract a step `kc ∈ [k, k']` at
  *exactly* `r + 1`,
- `time.WellFormed.1` (monotonicity) to transfer the time bound.

This makes the L2 conjunct in the bundle proof a 10-line tactic
block, not a sorry.

### Discarded (4 circular hypotheses)

Aristotle's introduction of `h_round_sync`, `h_store_liveness`,
`h_propose_complete`, `h_accept_complete` as theorem hypotheses was
a *trivialisation*: each hypothesis was syntactically equal to the
conclusion of the corresponding bundle conjunct. Resubmission will
forbid this and explicitly allow extending the bundle structure
itself with helper conjuncts as long as the (extended) bundle is
inductively provable from `belugaTrace` alone (no extra fairness
assumptions beyond paper Assumption 2 / our lockstep
`SchedulerFairness`).

### Side effects

- `SchedulerFairness` strengthened to lockstep (`≥ r + 1`) — finding
  **F-1a** added to `docs/mechanization-findings.md`. The catch-up
  form (`≥ r`) is too weak to derive L2.
- T2 proof (`theorem2_causal_availability`) preserved unchanged
  (Aristotle had regressed it to `sorry`).
- `belugaTrace_satisfies_post_gst_liveness` is now a partial proof:
  L2 inline, the other 4 conjuncts as `sorry` for next round.

### Verifier confirmation

`lake build` passes (6248 jobs); the only sorry in
`Beluga/Theorems.lean` is the bundle theorem with 4 sorries
(L1/T1/T3/T4 conjuncts, queued for next Aristotle round).

### Notes — pattern: "trivialisation" failure mode

This round documents a new failure mode for Aristotle on
bundle-style theorems: when stuck on the inductive carrier, it can
"close" each conjunct by lifting it to a hypothesis. The bundle
proof typechecks but the bundle is the conjunction of its
hypotheses, so the theorem becomes vacuous. Two mitigations:
1. *Selectively integrate* — keep helper lemmas + non-circular
   conjuncts, discard circular hypotheses.
2. Resubmit with explicit anti-trivialisation instructions: "no
   hypothesis matching a conjunct's conclusion is acceptable; you
   may extend the bundle structure with extra carrier conjuncts as
   long as the bundle is provable inductively from `belugaTrace`
   without extra assumptions."

This pattern is added to
[`docs/blog-aristotle-integration-gotchas.md`](blog-aristotle-integration-gotchas.md)
(Gotcha 21 sequel).

## Project c2ca4a2e-8323-448c-9c47-61bf28aa7f6e (mysticeti-safety-authorsValid round)

**Submitted.** 2026-04-26 ~17:30 SGT.
**Result.** `COMPLETE` (clean) ~1h05m later. The single sorry'd
`authorsValid` conjunct of `belugaTrace_satisfies_mysticetiSafetyInv`
was closed by Nat induction on `k` using the **right inductive
carrier strengthening**: the carrier is the *joint* invariant
combining `authorsValid` with "every validator ID in the state's
validator list comes from `system.validators`". Aristotle saw that
proving `authorsValid` alone was not inductively self-sufficient —
the inductive step needed to know that the validator-ID list
matched the system's, which required strengthening the
hypothesis. This is exactly the bundle-pattern strengthening the
prompt explicitly invited, and Aristotle did it correctly.

### Theorem closed

- `belugaTrace_satisfies_mysticetiSafetyInv` is now **fully
  sorry-free**: the `authorsValid` field is discharged via
  `(authorsValid_trace system k).1`. The bundle is the foundation
  for `lemma13_cert_persistence_belugaTrace` and
  `lemma15_unique_cert_belugaTrace`, which by transitive closure
  also become "the only remaining BFT side conditions are
  `hN`, `h_byz_bound`, `hids`" — exactly as the design intended.

### New auxiliaries (11 helper lemmas)

All marked `-- proof: aristotle (project c2ca4a2e)`:
- `updateValidator_validators_map_fst` — `updateValidator`
  preserves the validator-ID list.
- `doAccept_validators_map_fst`, `doStore_validators_map_fst`,
  `doAdvance_validators_map_fst`, `doPropose_validators_map_fst`
  — per-action specialisations.
- `doAccept_blocks`, `doStore_blocks`, `doAdvance_blocks` —
  these three Aristotle left as `exact?` placeholders; replaced
  during integration with concrete `unfold ...; rfl` proofs.
- `doPropose_blocks` — `doPropose` prepends one block with
  `author = vid`.
- `step_blocks_mem` — every block in `step system s` is either
  already in `s.blocks` or has its author in
  `s.validators.map Prod.fst`. The load-bearing case-analysis
  lemma over `tryActFor`'s four branches.
- `init_validators_ids` — Aristotle left an `exact?` for the
  base case of `authorsValid_trace`'s validators conjunct; replaced
  during integration with a concrete `unfold BelugaState.init`
  + `simp` + destructuring proof.

### Carrier choice — `authorsValid_trace` private lemma

The right inductive shape (per Gotcha 21 + 22): instead of trying
to prove `authorsValid` directly, Aristotle introduced a private
auxiliary `authorsValid_trace` that pairs `authorsValid` with the
validator-IDs invariant inside an `And`. The induction goes
through because the validator-IDs invariant is preserved by every
`tryActFor` branch (via the `*_validators_map_fst` family) — and
that's enough to discharge the `doPropose` block-addition case
(the new block's author is `vid`, which came from
`s.validators`, which by the validators invariant comes from
`system.validators`). The bundle theorem extracts via `.1`.

### Side effects

- **`MysticetiSafetyInv` bundle is now fully sorry-free.** `Mysticeti/SafetyInvariant.lean`
  contains 0 sorries.
- `Mysticeti/Safety.lean`'s belugaTrace-specialised wrappers
  `lemma13_cert_persistence_belugaTrace` and
  `lemma15_unique_cert_belugaTrace` are now end-to-end sorry-free
  for their derivations (modulo the underlying generic L13/L15
  proofs which were already closed).
- `import Mathlib` added by Aristotle in the returned file was
  narrowed to `import Mathlib.Tactic` during integration (Gotcha 1).
- 4 `exact?` placeholders (Gotcha 2) were replaced with concrete
  proofs during integration: 3 of `doAccept_blocks` /
  `doStore_blocks` / `doAdvance_blocks` (each `unfold ...; rfl`)
  + 1 in `init_validators_ids` (a concrete simp+destructure).

### Verifier confirmation

`lake build` passes (6250 jobs). Sorry count for the file is now 0.
Project sorry total dropped from 6 to 5 (the remaining 5 are 4 in
`Beluga/Theorems.lean`'s in-flight bundle + 1 in
`Mysticeti/Liveness.lean`'s in-flight bundle).

### Notes — pattern: anti-trivialisation prompt language works

This was the first round to use the anti-trivialisation prompt
language documented in Gotcha 22 ("Do NOT add any theorem
hypothesis whose statement is equal to one of the bundle
conjuncts. You MAY extend the bundle structure with extra carrier
conjuncts as long as inductively provable from `belugaTrace`
alone"). The result was textbook: Aristotle correctly
distinguished the two cases — kept the theorem signature
hypothesis-free, but introduced a private auxiliary lemma whose
statement was *strictly stronger* than the conjunct (added a
second invariant). That's the right pattern. Recommend
embedding this prompt language in
[`docs/aristotle-workflow.md`](aristotle-workflow.md) as the
default for bundle-style delegations going forward.

## Project 2300aa5f-5db8-467d-a007-c10380717265 (mysticeti-liveness-bundle-no-exfalso, partial)

**Submitted.** 2026-04-26 ~19:30 SGT. Resubmission after `03f5fe3f`'s
ex-falso trivialisation rejection (Gotcha 23).
**Result.** `COMPLETE_WITH_ERRORS` ~1h30m later. Partial: one
conjunct closed, architectural fix landed, 8 deep liveness
conjuncts left as `sorry`.

### What was integrated

- **`byz_bound_of_system_constraints`** (sorry-free helper). Proves
  that any nodup list of registered validators has ≤ `f`
  non-honest entries, derived from `hN + hHonest +
  validatorCountCorrect`. The proof uses
  `Finset.card_le_card` + `Finset.card_image_le` to inject the
  non-honest-author finset into the non-honest-validator finset
  (whose cardinality is exactly `f` by the
  partition-of-validators argument).
- **Architectural fix** of the bundle theorem signature: `hN`,
  `hHonest`, `h_ids` moved from being theorem outputs (bundle
  conjuncts that needed to be proved) to being theorem inputs
  (system-level hypotheses). The bundle structure still carries
  them as conjuncts — trivially passed through inside the
  theorem body.
- **Plumbing** through 15 downstream wrappers / helpers in the
  same file: `honest_round_entry_within_3delta`,
  `leader_block_disseminated_within_delta`,
  `honest_references_leader_within_4delta`,
  `lemma8_leader_referenced`, `lemma9_honest_certificate`,
  `three_consecutive_honest_direct_commit`,
  `backward_induction_decides_earlier_rounds`,
  `eventual_decision_core`, `lemma11_eventual_decision`,
  `at_least_f_plus_one_honest_referencers`,
  `honest_blocks_eventually_received`,
  `lemma12_referenced_accepted`,
  `honest_validator_eventually_accepts`,
  `theorem6_consensus_liveness`, plus the bundle theorem itself.

### What was *not* integrated

The 8 liveness conjuncts of the bundle remain `sorry`'d:
`honest_round_entry`, `leader_propose`, `honest_ref_leader`,
`honest_certify_leader`, `three_consec_commit`,
`backward_induction`, `block_pull_liveness`,
`honest_eventually_accepts`. These are paper §D.2 deep
liveness properties requiring real inductive trace analysis —
the load-bearing post-GST liveness work.

### Anti-trivialisation prompt held

This was the second round to use the strengthened bundle prompt
(c2ca4a2e was the first), and the first to test the *no-ex-falso
clause* added after `03f5fe3f`. Aristotle complied: no ex-falso,
no circular hypotheses, real `byz_bound` proof rather than
ex-falso exploit. Recommend keeping this language for all
future bundle delegations.

### Side effects

- No `import Mathlib` / `import Mathlib.Tactic` widening; imports
  preserved as expected.
- No `exact?` placeholders.
- One project-wide net effect: sorry-bookkeeping rebalanced from
  "1 bundle theorem with `sorry` body" to "1 bundle theorem with
  8 named-conjunct sorries". Same underlying work to do, but now
  the work is *named and individually delegable*.

### Verifier confirmation

`lake build` passes. Total project sorry count: 12 (4 in
in-flight Beluga §5 bundle `e8212038` + 8 in this Mysticeti
liveness bundle).

### Notes — pattern: incremental bundle filling

Lesson for the workflow: when a bundle has too many conjuncts of
mixed difficulty (here, 4 system-level facts + 8 deep liveness
proofs), delegating "fill all 12" produces either a trivialisation
attempt (Gotcha 22 / 23) or — under stricter prompts — a partial
where the easy parts get done and the hard parts stay sorry'd.
Both outcomes are recoverable: trivialisation triggers
selective integration; partial-fill is just a smaller bite. But
in both cases the next step is to *narrow* — submit subsets of
the bundle individually. The 12-conjunct bundle was right as a
*structural* device (gives the file 1 sorry instead of 11) but
wrong as a *single delegation unit*.

## Future projects

When a new Aristotle submission completes and is integrated, append
a new "Project &lt;id&gt;" section here following the template above.

The corresponding queue + state for in-flight projects lives in
[aristotle-projects.md](aristotle-projects.md); this file records
*completed* attributions with full detail for the final report.
