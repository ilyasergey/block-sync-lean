# Formalization overview

Lean 4 formalization of *Beluga: Block Synchronization for BFT Consensus
Protocols*.

## Paper → code map

The single source of truth for which paper item lives where in this repo.
Status: ✅ done · ◐ in progress · ☐ planned · ⊘ out of scope · ⏸ deferred.

### §2 — Network model and synchronizer abstraction

| Paper | Code | Status |
|---|---|---|
| §2 — Network model (`n`, `f`, `k`, `GST`, `Δ`) | [`System.lean :: BlockSynchroniserSystem`](BlockSynchroniser/System.lean#L22) | ✅ |
| §2 — Honest / Byzantine partition | [`System.lean :: isHonest` / `isByzantine`](BlockSynchroniser/System.lean#L58) | ✅ |
| §2.1 — Block structure (`r, d, author, parents, payload, signature`) | [`Block.lean :: Block`](BlockSynchroniser/Block.lean#L22) | ✅ — signature field omitted (see modeling notes). |
| §2.1 — Synchronizer interface (`block_propose_i`/`block_accept_i`/`block_store_i`) | [`Operations.lean :: ValidatorOperation`](BlockSynchroniser/Operations.lean#L17) | ✅ |
| §2.1 — Causal history `causal(B)` | [`Causal.lean :: Reaches` / `causal`](BlockSynchroniser/Causal.lean#L27) | ✅ |
| §2.1 — **Definition 1.1 — Round-Progression** | [`Properties.lean :: RoundProgression`](BlockSynchroniser/Properties.lean#L27) | ✅ |
| §2.1 — **Definition 1.2 — Round-Termination** | [`Properties.lean :: RoundTermination`](BlockSynchroniser/Properties.lean#L46) | ✅ |
| §2.1 — **Definition 1.3 — Block availability** | [`Properties.lean :: BlockAvailability`](BlockSynchroniser/Properties.lean#L65) | ✅ |
| §2.1 — **Definition 1.4 — Causal availability** | [`Properties.lean :: CausalAvailability`](BlockSynchroniser/Properties.lean#L79) | ✅ |
| §2.1 — **Definition 1** (block synchronizer = conjunction) | [`Properties.lean :: BlockSynchronizer`](BlockSynchroniser/Properties.lean#L93) | ✅ |

### §4 — The Beluga protocol

| Paper | Code | Status |
|---|---|---|
| §4.1 — Block extensions (`weaklinks`, `watermark`, `ancestors`) | [`Beluga/BlockExt.lean :: BelugaBlock`](BlockSynchroniser/Beluga/BlockExt.lean#L31) | ✅ |
| §4.2 — Reputation mechanism (Figure 8 lines 23–32) | [`Beluga/Reputation.lean`](BlockSynchroniser/Beluga/Reputation.lean#L23) | ✅ |
| §4.2 — Admission Control + parent selection (Figure 8 lines 14–17 + round-advancement rule (i)) | [`Beluga/AdmissionControl.lean`](BlockSynchroniser/Beluga/AdmissionControl.lean#L60) | ✅ |
| §4.3 — ImPoA + live/bulk classification | [`Beluga/Pull.lean`](BlockSynchroniser/Beluga/Pull.lean#L30) | ✅ — strong-link only. |
| §4 — `BelugaState`, `BelugaValidator`, `ReputationTable` | [`Beluga/State.lean`](BlockSynchroniser/Beluga/State.lean#L97) | ✅ |
| §4 — Protocol semantics: `HonestStep` (relational) + executable `step` + `belugaTrace` | [`Beluga/Protocol.lean`](BlockSynchroniser/Beluga/Protocol.lean#L186) | ✅ |
| §4 — Executable demos | [`Beluga/Examples.lean`](BlockSynchroniser/Beluga/Examples.lean#L17) | ✅ |
| §4.3 — Random pull complexity bound (`O(1)`) | — | ⊘ probabilistic |
| §4.4 — Availability pattern | [`Beluga/Patterns.lean :: availabilityPattern`](BlockSynchroniser/Beluga/Patterns.lean#L37) | ✅ — strong-link only. |
| §4.4 — Certificate pattern | [`Beluga/Patterns.lean :: certificatePattern`](BlockSynchroniser/Beluga/Patterns.lean#L48) | ✅ |
| §4.4 — `available` / `certified` | [`Beluga/Patterns.lean`](BlockSynchroniser/Beluga/Patterns.lean#L53) | ✅ |
| §4.4 — Uniqueness of certified blocks per `(author, round)` | [`Beluga/Patterns.lean :: certified_unique`](BlockSynchroniser/Beluga/Patterns.lean#L150) | ✅ |

### §5 — Beluga's main theorems

The §5 layer lives in [`Beluga/Theorems.lean`](BlockSynchroniser/Beluga/Theorems.lean)
and is stated against the network-aware trace
`networkBelugaTraceWithPull`. The protocol layer (state, step,
fairness derivation, named liveness primitives) lives in
[`Beluga/Network.lean`](BlockSynchroniser/Beluga/Network.lean).

| Paper | Code | Status |
|---|---|---|
| §5 hypothesis bundle (event-triggered post-GST liveness) | [`Beluga/Theorems.lean :: BelugaPartialSynchrony`](BlockSynchroniser/Beluga/Theorems.lean#L68) | ✅ |
| §5 strengthened bundle (adds the `T_rd = 5Δ` timeout) | [`Beluga/Theorems.lean :: BelugaWithPullFairness`](BlockSynchroniser/Beluga/Theorems.lean#L98) | ✅ |
| Pull mechanism (paper §4.3) explicit modelling | [`Beluga/Network.lean`](BlockSynchroniser/Beluga/Network.lean#L92) | ✅ |
| §5 — **Lemma 1** — round-entry within `4Δ` post-GST | [`Beluga/Theorems.lean :: lemma1_honest_round_entry`](BlockSynchroniser/Beluga/Theorems.lean#L1506) | ✅ |
| §5 — **Theorem 1** — Beluga ⊨ Block availability | [`Beluga/Theorems.lean :: network_theorem1_block_availability_withPull`](BlockSynchroniser/Beluga/Theorems.lean#L1856) | ✅ |
| §5 — **Theorem 2** — Beluga ⊨ Causal availability | [`Beluga/Theorems.lean :: network_theorem2_causal_availability_withPull`](BlockSynchroniser/Beluga/Theorems.lean#L2099) | ✅ |
| §5 — **Theorem 3** — Beluga ⊨ Round-Progression | [`Beluga/Theorems.lean :: network_theorem3_round_progression_withPull`](BlockSynchroniser/Beluga/Theorems.lean#L1923) | ✅ |
| §5 — **Theorem 4** — Beluga ⊨ Round-Termination | [`Beluga/Theorems.lean :: network_theorem4_round_termination_proved`](BlockSynchroniser/Beluga/Theorems.lean#L1805) | ✅ |
| §5 corollary — Beluga is a block synchronizer (T1∧T2∧T3∧T4) | [`Beluga/Theorems.lean :: beluga_isBlockSynchronizer`](BlockSynchroniser/Beluga/Theorems.lean#L2140) | ✅ |

### Appendix C — Performance bounds

| Paper | Code | Status |
|---|---|---|
| **Assumption 1 — latency triangle** | [`Beluga/PerformanceLemmas.lean :: LatencyTriangle`](BlockSynchroniser/Beluga/PerformanceLemmas.lean#L40) | ✅ |
| **Lemma 2** — honest validators are not blamed (post-GST) | [`Beluga/PerformanceLemmas.lean :: lemma2_honest_not_blamed`](BlockSynchroniser/Beluga/PerformanceLemmas.lean#L58) | ✅ |
| **Lemma 3** — round latency `Δ` when honest reputations dominate | [`Beluga/PerformanceLemmas.lean :: lemma3_round_latency_delta`](BlockSynchroniser/Beluga/PerformanceLemmas.lean#L108) | ✅ |
| **Lemma 4** — round latency `2Δ`-or-blame (deterministic part) | [`Beluga/PerformanceLemmas.lean :: lemma4_round_latency_or_blamed`](BlockSynchroniser/Beluga/PerformanceLemmas.lean#L150) | ✅ |
| **Lemma 5**, **Lemma 6**, **Theorem 5** — expected-latency bounds | — | ⊘ probabilistic. |

### Appendix D — Mysticeti-Beluga

| Paper | Code | Status |
|---|---|---|
| D.1.1 — Direct / indirect decision rules | [`Mysticeti/Consensus.lean :: directDecide` / `indirectDecideStep`](BlockSynchroniser/Mysticeti/Consensus.lean#L100) | ✅ |
| D.1.1 — Skip pattern / certificate pattern | [`Mysticeti/Consensus.lean :: skipPattern` / `certificatePatternAt`](BlockSynchroniser/Mysticeti/Consensus.lean#L44) | ✅ |
| D.1.2 — Round-robin leader schedule | [`Mysticeti/Consensus.lean :: leaderOf` / `isLeaderBlock`](BlockSynchroniser/Mysticeti/Consensus.lean#L27) | ✅ |
| **Lemma 7** — round-`r` honest leader's block is referenced by every honest round-`(r+1)` block | [`Mysticeti/Liveness.lean :: honest_ref_leader`](BlockSynchroniser/Mysticeti/Liveness.lean#L368) | ✅ |
| **Lemma 8** — round-`r` honest leader's block becomes certified | [`Mysticeti/Liveness.lean :: honest_certify_leader`](BlockSynchroniser/Mysticeti/Liveness.lean#L557) | ✅ |
| **Lemma 9** — round-robin pigeonhole (3 consecutive honest leaders in any 3f+3 window) | [`Mysticeti/Liveness.lean :: lemma9_round_robin_pigeonhole`](BlockSynchroniser/Mysticeti/Liveness.lean#L783) | ✅ |
| **Lemma 10** — eventual direct commit at every starting round | [`Mysticeti/Liveness.lean :: lemma10_eventual_commit`](BlockSynchroniser/Mysticeti/Liveness.lean#L1108) | ✅ — formalised in the form Theorem 6 consumes (post-GST, every starting round has a future round at which the leader's block direct-commits). |
| **Lemma 11** — block referenced by `2f+1` subsequent blocks ⇒ honest validators eventually `block_accept` it | [`Mysticeti/Liveness.lean :: lemma11_referenced_accepted`](BlockSynchroniser/Mysticeti/Liveness.lean#L1132) | ✅ |
| **Lemma 12** — certificate persistence across rounds | [`Mysticeti/Safety.lean :: lemma12_cert_persistence`](BlockSynchroniser/Mysticeti/Safety.lean#L100) | ✅ |
| **Lemma 13** — directly-skipped leader is never committed | [`Mysticeti/Safety.lean :: lemma13_no_commit`](BlockSynchroniser/Mysticeti/Safety.lean#L191) | ✅ |
| **Lemma 14** — no honest validator skips a directly-committed leader | [`Mysticeti/Safety.lean :: lemma14_no_skip`](BlockSynchroniser/Mysticeti/Safety.lean#L229) | ✅ |
| **Lemma 15** — at most one certified leader per round | [`Mysticeti/Safety.lean :: lemma15_unique_cert`](BlockSynchroniser/Mysticeti/Safety.lean#L269) | ✅ |
| **Lemma 16** — consistent leader-status decision across honest validators | [`Mysticeti/Safety.lean :: lemma16_consistent_status`](BlockSynchroniser/Mysticeti/Safety.lean#L336) | ✅ |
| **Theorem 6** — Mysticeti-Beluga consensus liveness | [`Mysticeti/Liveness.lean :: theorem6_consensus_liveness`](BlockSynchroniser/Mysticeti/Liveness.lean#L1176) | ✅ |
| **Theorem 7** — Mysticeti-Beluga consensus safety | [`Mysticeti/Safety.lean :: theorem7_consensus_safety`](BlockSynchroniser/Mysticeti/Safety.lean#L406) | ✅ |
| Mysticeti safety invariants for `belugaTrace` | [`Mysticeti/SafetyInvariant.lean :: belugaTrace_satisfies_mysticetiSafetyInv`](BlockSynchroniser/Mysticeti/SafetyInvariant.lean#L246) | ✅ |

## Not in the paper — internal validation

The `golden_*`, `realizable_*`, and `not_*_emptyTrace` lemmas in
[`Validation.lean`](BlockSynchroniser/Validation.lean#L57) are not
paper results. They are sanity checks demonstrating that our Lean
version of each Definition-1 property is satisfiable / falsifiable
by concrete traces (non-vacuity validation). All four `golden_*`
theorems are fully proved; the realizability and anti-witness
lemmas are also closed.

## Lean-side modeling notes

Places where the Lean encoding makes a paper-implicit assumption
explicit, or models a paper datatype slightly differently. None
implies a paper concern.

- **`signature` field on `Block` omitted** (paper §2.1). The paper's
  [`Block`](BlockSynchroniser/Block.lean#L22) carries six fields
  `(r, d, author, parents, payload, signature)`; ours carries the
  first five. Signature semantics are not invoked by any theorem
  we target.

- **`BelugaState.WellFormed system s`**: every entry in
  `s.validators` is registered in `system.validators`. The paper
  conflates state's validators with the system's by construction;
  our [`BelugaState`](BlockSynchroniser/Beluga/State.lean#L97) is
  a separate data type that doesn't enforce this, so we surface it
  as an explicit hypothesis.

- **§5 hypothesis bundles.**
  [Lemma 1](BlockSynchroniser/Beluga/Theorems.lean#L1506) consumes
  [`BelugaPartialSynchrony`](BlockSynchroniser/Beluga/Theorems.lean#L68);
  T1–T4 consume
  [`BelugaWithPullFairness`](BlockSynchroniser/Beluga/Theorems.lean#L98)
  which extends it with the `T_rd = 5Δ` timeout. Each field of each
  bundle corresponds to a paper-stated or paper-implicit primitive.

- **Lemma 5 split (Appendix C).** The paper's Lemma 5 mixes the
  probabilistic "expected latency" claim with the deterministic
  "or at least one malicious validator is blamed" disjunction. We
  formalize only the deterministic disjunct as
  [`lemma4_round_latency_or_blamed`](BlockSynchroniser/Beluga/PerformanceLemmas.lean#L145).

- **§D.2 hypothesis bundle.** The §D.2 liveness theorems are derived
  from
  [`MysticetiBelugaSynchrony`](BlockSynchroniser/Mysticeti/Liveness.lean#L54),
  which extends `BelugaWithPullFairness` with seven paper-stated
  primitives anchored across §4.2 (per-action liveness for
  `propose` / `store`), §D.1.2 (admission rule), §D.1.1 (cert-pattern
  timing), §2.1 + §D.3 (digest determinism), §2.1 + §4.2 (parents
  in pool), and §3 (honest non-equivocation). None is itself a §D.2
  conclusion.

- **Lemma 10 statement form.** Paper L10 ensures every undecided
  leader is eventually decided, supporting the §D.1.1 indirect-rule
  chain. We formalise it in the form Theorem 6 consumes
  ([`lemma10_eventual_commit`](BlockSynchroniser/Mysticeti/Liveness.lean#L1108)):
  post-GST, at every starting round there is a future round whose
  leader block direct-commits. T6 then derives every honest
  validator's eventual acceptance from this and the §5 in-pool
  delivery + §4.2 accept-action liveness, without invoking the
  indirect-rule chain.

- **Transaction order as a concrete function.** Paper §D.2 / §D.3
  treat the per-validator ordered transaction sequence abstractly.
  We define
  [`belugaTransactionOrderState`](BlockSynchroniser/Beluga/Order.lean#L35)
  as the canonical traversal of a validator's `block_accept`
  operations and prove order-faithfulness as a theorem rather than
  taking it as an abstract parameter.

- **L16 / T7 explicit hypotheses.** Paper
  [Lemma 16](BlockSynchroniser/Mysticeti/Safety.lean#L336)'s
  "consistent decisions" claim and
  [Theorem 7](BlockSynchroniser/Mysticeti/Safety.lean#L406)'s
  prefix-consistency of ordered sequences silently invoke decision
  completeness, view-traceback to a directly-decided leader, and
  order-respects-view-equality. We surface these as explicit
  hypotheses (`h_decision_complete`, `h_view_traceback`,
  `h_order_from_view`); for `belugaTrace` the order-from-view
  hypothesis is discharged by the concrete transaction-order
  construction above.

## Repository layout

```
block-sync-lean/
├── formalization.md            ← you are here
├── README.md                   ← build / run instructions
├── BlockSynchroniser/
│   ├── Block, Validator, Operations.lean
│   ├── System, State, Trace.lean
│   ├── Timing.lean             ← TimeMap, PartiallySynchronous
│   ├── Causal.lean             ← inductive Reaches / causal
│   ├── Quorum.lean             ← BFT quorum-intersection
│   ├── Properties.lean         ← Definition 1.1–1.4
│   ├── Validation.lean         ← non-vacuity sanity checks
│   ├── Beluga/
│   │   ├── BlockExt.lean       ← BelugaBlock (§4.1)
│   │   ├── Patterns.lean       ← available/certified (§4.4)
│   │   ├── State.lean          ← BelugaState + ReputationTable
│   │   ├── Reputation.lean     ← §4.2 update rules
│   │   ├── AdmissionControl.lean ← §4.2 parent selection
│   │   ├── Pull.lean           ← §4.3 ImPoA + live/bulk
│   │   ├── Protocol.lean       ← HonestStep + executable step
│   │   ├── Network.lean        ← network-aware §4 protocol layer
│   │   ├── Order.lean          ← canonical transaction order
│   │   ├── PerformanceLemmas.lean ← Appendix C lemmas
│   │   ├── Examples.lean       ← #eval smoke tests
│   │   └── Theorems.lean       ← §5 paper layer (L1, T1–T4)
│   └── Mysticeti/
│       ├── Consensus.lean      ← decision rules + leader schedule (D.1)
│       ├── Safety.lean         ← Lemmas 12–16, Theorem 7 (D.3)
│       ├── SafetyInvariant.lean ← Mysticeti safety invariants for belugaTrace
│       └── Liveness.lean       ← MysticetiBelugaSynchrony bundle +
│                                  Lemmas 7, 8, 9, 10, 11, Theorem 6 (D.2)
├── Main.lean                   ← drives the executable Beluga trace
├── lakefile.lean
└── lean-toolchain              ← v4.28.0
```

## Build

```bash
lake update
lake build
```

Toolchain pinned to `leanprover/lean4:v4.28.0`.

## Runnable examples

```bash
lake exe blocksynchroniser
```

Drives 20 executable `step` calls on a 4-validator, 1-Byzantine-budget
honest system (see [`BlockSynchroniser/Beluga/Examples.lean :: system4`](BlockSynchroniser/Beluga/Examples.lean#L17))
and prints the resulting operation log. The schedule is round-robin:
each step scans validators in id order and applies the first available
action (priority: propose → accept → store → advance).
