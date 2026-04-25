# Formalization Status — Paper Mapping

Precise mapping from [Beluga paper](Block_Sync_Project.pdf) to Lean targets, with status.

**Status legend:** ☐ planned · ◐ in progress · ✅ done · ⊘ out of scope · ⏸ deferred

Last updated: 2026-04-25 (initial).

## §2 — Problem definition (the abstraction)

| Paper | Lean target | Status | Notes |
|---|---|---|---|
| §2 — Network model: `n` validators, `f < n/3`, partial synchrony, GST, Δ | `BlockSynchroniser/System.lean :: BlockSynchroniserSystem` | ☐ | Need to add `GST : ℕ`, `Δ : ℕ` to existing struct |
| §2 — Threat model: pairwise-reliable channels, honest/Byzantine/crashed | `BlockSynchroniser/Validator.lean` | ☐ | Currently binary honest/byzantine; refine if needed |
| §2.1 — Block structure: `r, d, author, parents, payload, signature` | `BlockSynchroniser/Block.lean :: Block` | ◐ | Existing `Block` lacks `signature`; payload may be optional |
| §2.1 — Synchronizer interface: `block_propose_i(B,r)`, `block_accept_i(B.d)`, `block_store_i(B)` | `BlockSynchroniser/Operations.lean :: ValidatorOperation` | ✅ | Already correctly modeled |
| §2.1 — `causal(B)` (causal history) | `BlockSynchroniser/Causal.lean :: causal` | ◐ | Existing list-of-paths definition; replace with inductive `Reaches` |
| **Definition 1.1 — Round-Progression** | `BlockSynchroniser/Properties.lean :: RoundProgression` | ◐ | Existing as `blockSynchroniserProgressI`; needs rename + cleanup |
| **Definition 1.2 — Round-Termination** | `BlockSynchroniser/Properties.lean :: RoundTermination` | ◐ | Existing as `blockSynchroniserProgressII`; needs rename |
| **Definition 1.3 — Block availability** | `BlockSynchroniser/Properties.lean :: BlockAvailability` | ◐ | Existing as `blockSynchroniserAvailability`; rename |
| **Definition 1.4 — Causal availability** | `BlockSynchroniser/Properties.lean :: CausalAvailability` | ◐ | Existing as `blockSynchroniserCausalAvailability`; rename |
| §2.1 — Goal G1: Optimal push | (no formal target) | ⊘ | Performance goal, not a logical property |
| §2.1 — Goal G2: Bounded amplification | (no formal target) | ⊘ | Performance goal |

## §2.2 — Existing protocols (Multi-chain Certified, DAG-based Certified, RBC, Uncertified)

| Paper | Lean target | Status |
|---|---|---|
| §2.2.1–2.2.4 — Existing protocol descriptions | (none) | ⊘ Not formalized — used only for comparison in the paper |

## §3 — Pull induction attacks

| Paper | Lean target | Status |
|---|---|---|
| §3.1 — Pull induction attack scenario (Figure 2) | (none) | ⊘ Not a theorem; descriptive |
| §3.2 — Key insights 1, 2, 3 | (none) | ⊘ Design rationale |

## §4 — The Beluga Protocol

### §4.1 — Block-structure extensions

| Paper | Lean target | Status |
|---|---|---|
| §4.1 — `weaklinks`, `watermark[]`, `ancestors[]` | `BlockSynchroniser/Beluga/BlockExt.lean :: BelugaBlock` | ☐ |

### §4.2 — AC-based Optimistic Push

| Paper | Lean target | Status |
|---|---|---|
| §4.2 — Reputation increase/decrease rules | `BlockSynchroniser/Beluga/Reputation.lean` | ☐ |
| §4.2 — Admission control: parent selection, threshold `R_t` | `BlockSynchroniser/Beluga/AdmissionControl.lean` | ☐ |
| §4.2 — Round-advancement rules (i), (ii) | `BlockSynchroniser/Beluga/AdmissionControl.lean :: roundAdvance` | ☐ |
| Appendix E (Figure 8) — pseudocode for `create_new_block`, `AC_parent_selection`, `compute_ancestors`, `update_score_with_watermarks` | inlined into the modules above | ☐ |

### §4.3 — ImPoA-based Hybrid Pull

| Paper | Lean target | Status |
|---|---|---|
| §4.3.1 — Implicit PoA: B referenced by ≥ f+1 subsequent blocks | `BlockSynchroniser/Beluga/Pull.lean :: implicitlyAvailable` | ☐ |
| §4.3.1 — Live vs bulk block classification | `BlockSynchroniser/Beluga/Pull.lean :: classifyBlock` | ☐ |
| §4.3.2 — Hybrid pull strategy: deterministic (live) + randomized (bulk) | `BlockSynchroniser/Beluga/Pull.lean` | ◐ Deterministic side only; random side ⊘ (probabilistic) |

### §4.4 — Block patterns

| Paper | Lean target | Status |
|---|---|---|
| §4.4 — Availability pattern (referenced by > f distinct validators) | `BlockSynchroniser/Beluga/Patterns.lean :: availabilityPattern` | ☐ |
| §4.4 — Certificate pattern (referenced as parents by > 2f distinct validators) | `BlockSynchroniser/Beluga/Patterns.lean :: certificatePattern` | ☐ |
| §4.4 — `available B` / `certified B` predicates | `BlockSynchroniser/Beluga/Patterns.lean` | ☐ |
| §4.4 — Uniqueness of certified per (author, round) (mentioned, used by safety) | `BlockSynchroniser/Beluga/Patterns.lean :: certified_unique` | ☐ |

## §5 — Protocol Analysis (the main theorems)

| Paper | Statement | Lean target | Status |
|---|---|---|---|
| **Lemma 1** | After GST, all honest validators enter the same round within 3Δ | `BlockSynchroniser/Beluga/Theorems.lean :: lemma1_honest_round_entry` | ☐ |
| **Lemma 2** | After GST, round-to-round latency ≤ 3Δ in happy case | `BlockSynchroniser/Beluga/Theorems.lean :: lemma2_round_latency` | ☐ |
| **Theorem 1** | Block availability (Beluga ⊨ Def 1.3) | `BlockSynchroniser/Beluga/Theorems.lean :: theorem1_block_availability` | ☐ |
| **Theorem 2** | Causal availability (Beluga ⊨ Def 1.4) | `BlockSynchroniser/Beluga/Theorems.lean :: theorem2_causal_availability` | ☐ |
| **Theorem 3** | Round-Progression (Beluga ⊨ Def 1.1) | `BlockSynchroniser/Beluga/Theorems.lean :: theorem3_round_progression` | ☐ |
| **Theorem 4** | Round-Termination (Beluga ⊨ Def 1.2) | `BlockSynchroniser/Beluga/Theorems.lean :: theorem4_round_termination` | ☐ |

## Appendix C — Performance Analysis

| Paper | Statement | Status | Reason |
|---|---|---|---|
| Lemma 3 | After GST, honest reputation ≥ malicious | ⊘ | Worst-case version provable, but skipped — not central |
| Lemma 4 | Future round latency = Δ when reputation gap holds | ⊘ | Worst-case version provable, but performance bound |
| Lemma 5 | Round latency ≤ 2Δ except when malicious blamed | ⊘ | As above |
| Lemma 6 | Future expected latency within 2Δ or one malicious blamed | ⊘ | "Expected" — probabilistic, out of scope |
| Lemma 7 | Malicious can only delay finitely many rounds with expected latency > 2Δ | ⊘ | Probabilistic |
| Theorem 5 | Under adverse, average round latency ≈ 2Δ | ⊘ | Asymptotic + probabilistic |

## Appendix D — Security Analysis of Mysticeti-Beluga

### D.1 — Build Mysticeti on Beluga (definitional content)

| Paper | Lean target | Status |
|---|---|---|
| D.1.1 — Direct/indirect decision rules; commit/skip status | `BlockSynchroniser/Mysticeti/Consensus.lean :: decisionRule` | ☐ (Phase 6) |
| D.1.2 — Round-robin leader schedule | `BlockSynchroniser/Mysticeti/Consensus.lean :: leaderSchedule` | ☐ (Phase 6) |
| D.1.2 — Round advancement conditions (i)/(ii); timeout `T_live = max(T_id, T_rd)` | `BlockSynchroniser/Mysticeti/Consensus.lean` | ☐ (Phase 6) |
| D.1.2 — Parent selection (consensus-specified, refers round-2 leader) | `BlockSynchroniser/Mysticeti/Consensus.lean` | ☐ (Phase 6) |

### D.2 — Liveness (Theorem 6)

| Paper | Statement | Status |
|---|---|---|
| Lemma 8 | After GST, an honest leader's block is referenced next round by every honest validator | ⏸ Deferred (depends on timing model + pull) |
| Lemma 9 | After GST, all honest validators create a certificate for an honest leader's block | ⏸ |
| Lemma 10 | Round-robin schedule has 3 consecutive honest-leader rounds in any 3f+3 window | ☐ Phase 6 — pure pigeonhole, no deps |
| Lemma 11 | Any undecided leader block eventually gets decided | ⏸ |
| Lemma 12 | If B referenced by 2f+1 subsequent blocks, every honest validator outputs `block_accept` | ⏸ |
| **Theorem 6** | Mysticeti-Beluga consensus liveness | ⏸ Deferred — composes everything |

### D.3 — Safety (Theorem 7)

| Paper | Statement | Lean target | Status |
|---|---|---|---|
| Lemma 13 | Certificate persistence across rounds | `BlockSynchroniser/Mysticeti/Safety.lean :: lemma13_cert_persistence` | ☐ Phase 6 |
| Lemma 14 | No honest validator skips a directly-committed leader | `BlockSynchroniser/Mysticeti/Safety.lean :: lemma14_no_skip` | ☐ Phase 6 |
| Lemma 15 | At most one certified leader per round | `BlockSynchroniser/Mysticeti/Safety.lean :: lemma15_unique_cert` | ☐ Phase 6 |
| Lemma 16 | Consistent leader-status decision across honest validators | `BlockSynchroniser/Mysticeti/Safety.lean :: lemma16_consistent_status` | ☐ Phase 6 |
| **Theorem 7** | Mysticeti-Beluga consensus safety | `BlockSynchroniser/Mysticeti/Safety.lean :: theorem7_consensus_safety` | ☐ Phase 6 |

## Appendix E–G

Pseudocode (E), implementation (F), and experimental setup (G) are not theorem-bearing — content from E is inlined into the Beluga modules where applicable.

## Validation lemmas (non-vacuity defenses)

| Target | Lean target | Status |
|---|---|---|
| `goldenTrace` — concrete honest run with `n=4, f=1` | `BlockSynchroniser/Validation.lean :: goldenTrace` | ☐ |
| `goldenTrace ⊨ RoundProgression ∧ … ∧ CausalAvailability` | `Validation.lean :: goldenTrace_satisfies_all` | ☐ |
| `realizable_propose`, `realizable_accept`, `realizable_store` | `Validation.lean` | ☐ |
| `emptyTrace ⊭ RoundProgression` | `Validation.lean :: empty_fails_progression` | ☐ |
| `byzantineOnlyTrace ⊭ RoundTermination` | `Validation.lean :: byz_fails_termination` | ☐ |

## Summary counts

| Category | Total | Done | In progress | Planned | Out of scope/deferred |
|---|---|---|---|---|---|
| §2 abstraction | 11 | 1 | 5 | 3 | 2 |
| §4 Beluga protocol | 12 | 0 | 1 | 11 | 0 |
| §5 main theorems | 6 | 0 | 0 | 6 | 0 |
| Appendix C performance | 6 | 0 | 0 | 0 | 6 |
| Appendix D safety bundle | 5 | 0 | 0 | 5 | 0 |
| Appendix D liveness | 5 | 0 | 0 | 0 | 5 |
| Validation | 5 | 0 | 0 | 5 | 0 |
| **Totals** | **50** | **1** | **6** | **30** | **13** |
