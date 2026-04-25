# Formalization Plan: Beluga Block Synchronizer

Plan for formalizing the key definitions and theorems from
[*Beluga: Block Synchronization for BFT Consensus Protocols*](Block_Sync_Project.pdf)
in Lean 4.

## Goals

1. Formalize the **block synchronizer abstraction** (Definition 1, §2.1) — the four properties any block synchronizer must satisfy: *Round-Progression*, *Round-Termination*, *Block availability*, *Causal availability*.
2. Define the **Beluga protocol** (§4) at the level of a transition system: AC-based optimistic push with reputation/admission control, ImPoA-based hybrid pull (live + bulk modules).
3. Prove the **main theorems** (§5): Lemma 1, Lemma 2, Theorems 1–4 — Beluga satisfies the abstraction.
4. **Stretch**: Mysticeti-Beluga safety bundle from Appendix D (Lemmas 10, 13, 14, 15, 16, Theorem 7) — purely combinatorial, no probability.

## Scope decisions

| Topic | Decision |
|---|---|
| Time model | `ℕ` (not `ℝ≥0`); GST and Δ are natural-number bounds |
| Adversary model | Quantify over arbitrary traces; honest steps must follow protocol; everything else is "Byzantine" |
| Probabilistic content | **Excluded** from proofs. Documented as future work in [README.md](../README.md). Affects: random pull complexity bound, Appendix C performance theorems (L6, L7, T5) |
| Mysticeti-Beluga liveness (Appendix D liveness side) | Out of scope for v1 — depends on Beluga T1/T2 *and* timing model; revisit after the safety bundle |
| Performance theorems (Appendix C) | Out of scope. L3, L4, L5 may be reachable as deterministic worst-case statements; L6, L7, T5 are inherently probabilistic |

## Top-level file layout

```
BlockSynchroniser/
  Block.lean              -- Block structure, BlockDigest
  Validator.lean          -- ValidatorId, honest/byzantine classification
  System.lean             -- BlockSynchroniserSystem (n, f, k, GST, Δ)
  Operations.lean         -- ValidatorOperation = propose | accept | store
  State.lean              -- SystemState typeclass + DefaultSystemState
  Causal.lean             -- Reaches, parents, causal(B)
  Quorum.lean             -- Quorum predicate, quorum-intersection lemma
  Trace.lean              -- Trace, time map, traceInduction, Eventually
  Properties.lean         -- The 4 properties of Definition 1
  Validation.lean         -- goldenTrace, realizability lemmas, anti-witnesses
  Beluga/
    BlockExt.lean         -- Beluga's extra fields: weaklinks, watermark, ancestors
    Patterns.lean         -- availability pattern, certificate pattern
    Reputation.lean       -- reputation table, increment/decrement rules
    AdmissionControl.lean -- AC_parent_selection, round advancement
    Pull.lean             -- ImPoA, live/bulk classification
    Protocol.lean         -- Honest-validator transition relation
    Theorems.lean         -- Lemma 1, 2; Theorems 1–4
  Mysticeti/              -- (Phase 6, optional)
    Consensus.lean        -- direct/indirect decision rules, leader schedule
    Safety.lean           -- Lemmas 10, 13–16; Theorem 7
```

## Auxiliary definitions (build these early — load-bearing)

These will be reused across most theorems. Get them right in Phase 1.

- `Quorum` (set/list of ≥ `2f+1` distinct validators) — and the **quorum-intersection lemma**: any two quorums share ≥ `f+1` validators, hence ≥ 1 honest. This is the single most-used lemma in BFT proofs.
- `Reaches state B B'` — inductive transitive parent-of relation. Replaces the current ad-hoc `Path` / `isValidPath` code.
- `Eventually p k` := `∃ k' ≥ k, p k'` — combinator over traces. Cleans up every Definition-1 property.
- `EmittedAt trace k op` — predicate that operation `op` appears in trace at step `k`.
- `HasAccepted trace vid d` / `HasStored trace vid B` — derived from operations.
- `RoundOf state d` — partial map digest → round.
- `DistinctAuthors blocks` — extracted from blocks (cleans up Round-Termination).
- `byTime trace t` — index into trace by clock time, not step number.

## Phased plan

### Phase 0 — Cleanup (small, mechanical) ☐

- Revert `state_kz` typo at `BlockSynchroniser/Definitions.lean:228`.
- Delete `BlockSynchroniser/Existing/` entirely (legacy, not imported, depends on now-disabled `ssreflect`).
- Delete `blockSynchroniserValidity` (not in Def 1) and `blockSynchroniserCommonSet` (derivable; not in Def 1).
- Verify `lake build` is clean.

### Phase 1 — Core abstraction (paper §2) ☐

- Split monolithic `Definitions.lean` per file layout above.
- Add `GST : ℕ` and `Δ : ℕ` to `BlockSynchroniserSystem`. Add `time : ℕ → ℕ` (monotone, unbounded) on `Trace`.
- Replace `isValidPath`/`causal` with inductive `Reaches`. Prove well-foundedness via decreasing rounds.
- Define `Quorum` and prove `quorumIntersection`.
- Build the auxiliary combinators (`Eventually`, `EmittedAt`, etc.).

### Phase 2 — The four properties + validation (paper Definition 1) ☐

- State `RoundProgression`, `RoundTermination`, `BlockAvailability`, `CausalAvailability` to match the paper text exactly.
- Define `BlockSynchronizer S` = a trace satisfying all four.
- **Validation (non-vacuity)**:
  - **(A)** Construct `goldenTrace : Trace DefaultSystemState` — a concrete honest, synchronous run with `n = 4, f = 1` over a few rounds. Prove `goldenTrace ⊨` each property.
  - **(B)** For each property `P → ∃ Q`, prove a `realizable_*` sibling lemma showing the antecedent is reachable in some trace.
  - **(C)** Construct `emptyTrace` and `byzantineOnlyTrace`; prove they fail at least one property.

### Phase 3 — Beluga block extensions and patterns (§4.1, §4.4) ☐

- Extend `Block` with `weaklinks`, `watermark : Vector Round n`, `ancestors : Vector Round n`.
- Define `availabilityPattern` (referenced by > f distinct authors), `certificatePattern` (referenced as parents by > 2f distinct authors).
- Define `available B` and `certified B` predicates.
- **Key lemma (uniqueness of certified per round/author)** from quorum intersection — used by every later safety result.

### Phase 4 — Beluga protocol (§4.2–4.3) ☐

- `ReputationTable := ValidatorId → ℕ` with increment/decrement rules from §4.2 (matching pseudocode in Figure 8, Appendix E).
- `AdmissionControl`: `AC_parent_selection`, threshold `R_t := R_{2f+1} - R_L`, round-advancement conditions (i)/(ii).
- `ImPoA`: `implicitlyAvailable B` (referenced by ≥ f+1 blocks from subsequent rounds); live vs bulk classification.
- `HonestStep system trace k`: a single-predicate small-step *relation* specifying when step `k` of the trace is consistent with honest semantics. **Used by theorems.**
- `step : BlockSynchroniserSystem → BelugaState → BelugaState`: an *executable* implementation of one valid honest schedule. **Used to run the protocol** (`#eval`, `Main.lean` driver) and to construct concrete traces.
- **Refinement lemma**: every transition produced by `step` satisfies `HonestStep`. Connects the executable model to the relational model and serves as a constructive witness that `HonestStep` is non-vacuous.

### Phase 5 — Main theorems (§5) ☐

In dependency order:

- **L1**: After GST, all honest validators enter the same round within 3Δ.
- **L2**: After GST, round-to-round latency ≤ 3Δ in the happy case.
- **T3 (Round-Progression)**: induction on rounds, uses L1.
- **T4 (Round-Termination)**: uses T3 + admission control.
- **T1 (Block availability)**: pull protocol terminates for accepted blocks.
- **T2 (Causal availability)**: induction on causal depth, uses T1.

After each: re-prove the corresponding Phase-2 validation lemma against the protocol-induced trace generator (closes the loop).

### Phase 6 — Mysticeti-Beluga safety bundle (Appendix D) — stretch ☐

In dependency order:

- **L10** (round-robin pigeonhole) — pure Lean, no Beluga dep. Tractable starter.
- **L15** (at most one certified leader per round) — quorum intersection.
- **L13** (certificate persistence across rounds) — quorum intersection + induction.
- **L14** (no honest skips a directly-committed leader) — quorum intersection.
- **L16** (consistent leader-status decision) — backward induction; uses L11 (liveness; out of scope) ⇒ assume as hypothesis or shrink statement.
- **T7 (Consensus Safety)** — corollary of L16.

L8, L9, L11, L12, T6 (the liveness side of Appendix D) are deferred — they require both the timing model and the pull formalization.

## Validation strategy (how we avoid vacuous truth)

Every property of the form `P → ∃ Q` is satisfied by the empty trace. Defense in depth:

1. **Witness trace (A)**: `goldenTrace` with concrete `n, f, k` — proved to satisfy *all four* Definition-1 properties non-trivially. If existentials don't get filled with real values, the proof won't go through.
2. **Realizability (B)**: For each property, an existence lemma showing the antecedent is *reachable* in some trace.
3. **Anti-witnesses (C)**: `emptyTrace`, `byzantineOnlyTrace` — proven to *fail* at least one property. Catches under-specification.
4. **(Optional) Decidability**: bound traces by step count; make properties `Decidable` so `#eval` becomes a smoke test.

(A) + (B) are mandatory and ship next to each property in `Properties.lean`. (C) lives in `Validation.lean`.

## Aristotle policy

See [aristotle-workflow.md](aristotle-workflow.md) for full operational notes. In short:

- **Do ourselves**: all definitions/structures, the four properties, validation scaffolding, quorum-intersection lemma, trivial proofs.
- **Delegate**: pure-combinatorial lemmas (L10, L13–15), backward inductions on quorum reasoning (L16, T7), large pull/availability proofs (T1, T2), tedious list/Finset auxiliaries.
- **Hybrid**: timing lemmas (L1, L2), the four main Beluga theorems — try by hand with a `PROVIDED SOLUTION` sketch; fall back to delegation if it bogs down.

## Tracking progress

- Status of each item: [formalization-status.md](formalization-status.md) — keep this file in sync with reality.
- After every successful stage: add a timestamped entry to [../changelogs/](../changelogs/).
