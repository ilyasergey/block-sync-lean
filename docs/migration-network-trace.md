# Migration plan — §5 theorems against `networkTrace` — PARTIAL

> **Status update.** Phases 1–6 (the §5-on-networkTrace migration)
> are complete. Phases 7–13 (the **explicit pull mechanism** to
> discharge `EventualCausalAcceptance` and `EventualRoundAcceptance`
> as theorems rather than axioms) are in progress: Phases 7–9
> (model and primitive states) done, Phases 10–13 (proofs and
> integration) ahead.

## Pull mechanization (Phases 7–13)

Goal: replace the `EventualCausalAcceptance` /
`EventualRoundAcceptance` Prop hypotheses on T2/T4 with derived
theorems, using the explicit pull mechanism (paper §4.3).

### Phase 7 — `NetworkState` extension (DONE, commit `0075618`)

`PullRequest` type + `pullRequestsInflight` /
`pullRequestsInbox` fields on `NetworkState`. Helpers `pullInbox`,
`appendToPullInbox`, `removeFromPullInbox`. Existing networkTrace
proofs unaffected (new fields default to empty).

### Phase 8 — Pull semantics (DONE, commit `2074303`)

- `deliverPullPending`: drains pull requests to responder inboxes.
- `doPullRequest`: schedule pull requests for a digest.
- `doPullResponse`: process a request, schedule block_propose delivery.
- `pullCandidate`: identify a digest the validator wants but doesn't
  have / hasn't requested.
- `pullStepOne`, `pullStep`: per-validator and per-step pull actions.
- `networkStepWithPull`: alternate step calling `deliverPullPending`
  + `pullStep` before `networkTryActFor`.
- `networkTraceWithPull`: trace using the with-pull step.
- Preservation lemmas for currentTime and base across all new
  operations.

### Phase 9 — Pull liveness primitives (DONE, commit `3ea8b18`)

Three paper-faithful primitives in `Beluga/Network/Fairness.lean`:

- `PullRequestDelivery`: pull-channel `Δ`-bounded delivery (mirror
  of `NetworkDelivery` for pull requests).
- `PullResponseScheduling`: honest responders process pullInbox
  within `Δ` post-GST.
- `AcceptScheduling`: honest validators with acceptable blocks
  fire `doAccept` within `Δ` post-GST.

#### Total primitive count

**Six paper-named primitives** discharge T2/T4 once the iteration
proofs (Phase 10/11) are written:

| # | Primitive | Paper reference | Status |
|---|---|---|---|
| 1 | `NetworkDelivery` | §2 Δ-delivery | Pre-existing |
| 2 | `ActionScheduling` | §4.2 round-advance | Pre-existing |
| 3 | `BoundedRoundSpread_networkTrace` | §4.2 + F-1b | Pre-existing |
| 4 | `AcceptScheduling` | §4.2 accept-action | NEW (Phase 9) |
| 5 | `PullRequestDelivery` | §4.3 pull-channel | NEW (Phase 9) |
| 6 | `PullResponseScheduling` | §4.3 pull-response | NEW (Phase 9) |

Three are genuinely new for the §4.3 pull mechanization. The
`*WithPull` restatements that thread these through `networkTraceWithPull`
are not new paper-level assumptions, just trace-substitutions of
the same primitives.

### Phase 10 — Prove `EventualRoundAcceptance` (PENDING)

Proof sketch:
1. Apply `ActionScheduling` iteratively to bring every honest
   validator past round r+1 (so they all proposed for round r).
2. By `NetworkDelivery`, every honest round-r block_propose op is
   delivered to vid's inbox within Δ.
3. Each delivered block in pool is canAcceptBlock-acceptable for vid
   (vid hasn't accepted; vid has received via push).
4. Apply `AcceptScheduling` iteratively: vid's accept fires for
   each, within Δ.
5. By `system.honestBound ≥ 2f+1`, vid has accepted ≥ 2f+1 distinct
   honest authors' round-r blocks.

Estimated: ~200-500 lines.

### Phase 11 — Prove `EventualCausalAcceptance` (PENDING)

Proof sketch (induction on causal-ancestor depth):
1. Base: B' = B. vid has accepted B (given).
2. Step: vid has accepted some block B'' that has B' as a
   parent-set member.
   - If vid hasn't received B' via push: vid has a `pullCandidate`
     B'. Apply `PullScheduling` (pullStepOne fires): vid issues
     pull request.
   - By `PullRequestDelivery`: pull request reaches every honest
     responder's pullInbox within Δ.
   - At least one honest responder vid_resp has B' in pool (pool
     is global).
   - Apply `PullResponseScheduling`: vid_resp processes the
     request, schedules a `block_propose` delivery to vid.
   - By `NetworkDelivery` (for pull responses): vid's inbox
     contains B' within Δ.
   - Apply `AcceptScheduling`: vid accepts B' within Δ.

Estimated: ~300-700 lines (the induction on causal depth is the
new structural piece).

### Phase 12 — Integrate (PENDING)

Update `Beluga/Network/Theorems.lean`'s T2/T4 to use the proved
theorems from Phase 10/11 instead of the `Eventual*` axiom
hypotheses. The §5 corollary `networkTrace_isBlockSynchronizer`
loses two of its hypothesis parameters.

### Phase 13 — Cleanup + final docs (PENDING)

Decide whether to keep both `networkTrace` and `networkTraceWithPull`
or unify under the with-pull version. Update `formalization.md`
and `mechanization-findings.md` (specifically F-1c) to reflect the
fully-derived T2/T4. Update changelogs.

### Phase 14 — Bundle primitives (DONE early, commit `143dce5`)

The six paper-named primitives are now bundled into a single
record, mirroring the existing conclusion-side
`BelugaPostGSTLiveness` bundle on the primitive side:

```lean
structure PartiallySynchronousFairness
    (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop where
  -- §2 network model
  networkDelivery        : NetworkDelivery system time
  pullRequestDelivery    : PullRequestDelivery system time
  -- §4.2 protocol fairness
  actionScheduling       : ActionScheduling system time
  acceptScheduling       : AcceptScheduling system time
  -- §4.3 pull mechanism
  pullResponseScheduling : PullResponseScheduling system time
  -- F-1b structural invariant
  boundedRoundSpread     : BoundedRoundSpread_networkTrace system time
```

**Naming**: `PartiallySynchronousFairness` generalizes the existing
`PartiallySynchronous` typeclass to a record carrying all
paper-stated post-GST primitives — the single name communicates
"all assumptions about partial synchrony + honest validators
acting promptly".

**Refactored consumers**: `Beluga/Network/Theorems.lean`'s §5
wrappers (`network_lemma1_honest_round_entry`,
`network_lemma2_round_latency`,
`network_theorem1_block_availability`,
`network_theorem3_round_progression`,
`networkTrace_isBlockSynchronizer`) now take this single
`h_prim : PartiallySynchronousFairness` hypothesis instead of
threading 3 individual primitives. Internal proof bodies
destructure `h_prim.networkDelivery`, `h_prim.actionScheduling`,
`h_prim.boundedRoundSpread` etc. as needed. The `network_theorem4`
and `network_theorem2` still take their individual `Eventual*`
hypotheses pending Phases 10–11 (which will replace them with
proofs that consume `h_prim.acceptScheduling`,
`h_prim.pullRequestDelivery`, `h_prim.pullResponseScheduling`).

**Pulled forward from post-10/11 to before-10/11** on user
request: simplifies the calling convention before the remaining
proofs land. The Phase 10/11 proofs will destructure `h_prim`
the same way the existing wrappers do.

**Alternative considered** — group by paper section
(`NetworkChannelDelivery`, `ProtocolFairness`, plus a standalone
`BoundedRoundSpread`): more paper-faithful structurally but more
boilerplate and less alignment with the existing single-bundle
pattern. We chose the single-bundle approach for symmetry with
`BelugaPostGSTLiveness`.

**Future companion projections**: per-field projection lemmas like
`PartiallySynchronousFairness.implies_NetworkDelivery` could be
added if callers want individual fields without the verbose
`h_prim.networkDelivery` syntax. Not added now since the
field-access syntax is already clean.

---



> **Goal.** All §5 paper theorems (L1, L2, T1, T2, T3, T4, bundle,
> isBlockSynchronizer) stated against `networkTrace` (or its base
> projection), with all proofs derived from
> `Network.schedulerFairness_holds` plus structural invariants of
> `networkTrace`. No `NetworkBelugaCoherence` axiom; no sorries
> in `Beluga/`.
>
> **Status: complete.** All six phases delivered. The new canonical
> §5 derivations live in
> [`BlockSynchroniser/Beluga/Network/Theorems.lean`](../BlockSynchroniser/Beluga/Network/Theorems.lean).

## Final state

- `Beluga/Network/Theorems.lean`: 9 §5 entry points
  (`network_lemma1_honest_round_entry`, `network_lemma2_round_latency`,
   `network_theorem1_block_availability`,
   `network_theorem2_causal_availability`,
   `network_theorem3_round_progression`,
   `network_theorem4_round_termination`,
   `networkTrace_isBlockSynchronizer`, plus the `networkBelugaTrace`
   projection and two paper-implicit liveness axioms).
- `Beluga/Network/Fairness.lean`: 18 helper theorems on
  `networkStep` and `networkTrace` (round monotonicity, advance
  inversion, persistence, intermediate value, find-advance-step,
  all-honest-eventually-at-round, proposed-for-monotone, etc.).
- `Beluga/Theorems.lean`: trimmed to 1416 lines (was 2075). Helpers
  retained; §5 wrappers + bundle + `belugaTrace_isBlockSynchronizer`
  deleted.
- `Beluga/Network/Fairness.lean`: trimmed by ~170 lines.
  `NetworkBelugaCoherence`, `SchedulerFairness_belugaTrace`, and
  `belugaTrace_schedulerFairness` deleted (no longer needed once
  the §5 conclusions are about `networkTrace.base`).
- Build: clean, zero sorries in `Beluga/`.

## Paper-faithfulness summary

The §5 conclusions are now stated against the `networkTrace`
projection. The proofs route through:

- **`schedulerFairness_holds`** (proved theorem, Phase 5/6 of the
  Phase E network model) for L1/L2/T3 — the round-progression
  argument is fully derived from the network-trace primitives
  (NetworkDelivery, ActionScheduling, BoundedRoundSpread).
- **Structural invariants** for T1 — `network_acceptedBlockExists_trace`
  (a single conjunct of the `AcceptInv` chain that survives ImPoA),
  combined with `networkStep_advance_implies_stored` (Phase 2's
  inversion projection) and emittedOperations monotonicity.
- **Explicit liveness hypotheses** for T2 and T4 —
  `EventualCausalAcceptance` and `EventualRoundAcceptance` are
  Prop-level parameters capturing the paper-implicit pull-mechanism
  liveness claim that's not derivable from the structural model
  alone (paper §4.3 ImPoA + pull). These are the "honest, named
  axioms" surfacing the paper's hand-wave; see F-1c in
  `mechanization-findings.md`.

## Known limitations (paper-side)

Two paper-faithfulness gaps remain, both surfaced as named typed
hypotheses rather than buried in the proof:

1. **`EventualCausalAcceptance`** (T2): under ImPoA's f+1
   references rule, a validator can accept a block without
   directly accepting its parents. The paper's §5 T2 prose proof
   invokes the §4.3 pull mechanism to argue eventual acceptance.
   Mechanizing this requires modeling pull explicitly; we surface
   it as a typed Prop hypothesis.

2. **`EventualRoundAcceptance`** (T4): under the `T_rd = 4Δ`
   timeout (paper §4.2), a validator may advance its round
   without first accepting 2f+1 round-`r` blocks; the 2f+1
   acceptances arrive later via pull. Same structural reason
   as (1); same resolution.

These are equivalent to F-1c (`NetworkBelugaCoherence` was the
analogous axiom for the round-progression slice) in spirit: the
paper's two informal abstractions (network model vs. simpler
§5 prose model) are silently equated, and where they diverge,
mechanization needs explicit liveness assumptions.

## Phase-by-phase commit log

### Phase 1 — Foundational `networkStep` lemmas (10 helpers)

- `deliverPending_preserves_base` (commit `d65b2a5`)
- `networkTryActFor_round_monotone` + `_at_most_one` (commit `fea1f3b`)
- `networkStep_round_monotone` (commit `aa8bb53`)
- `networkStep_round_at_most_one` (commit `be42b5a`)
- `network_round_monotone_trace` (commit `5233197`)
- `network_honest_validator_persistent_trace` (commit `1dd5432`)
- `network_round_intermediate_value` (commit `b75c03a`)
- `networkStep_emittedOperations_monotone` (commit `6a2e482`)
- `networkStep_preserves_none` (commit `5d747da`)

### Phase 2 — Step inversion (188-line theorem + 3 projections)

- `networkStep_advance_inversion` + `*_implies_hasProposedFor` /
  `_stored` / `_gate` (commit `7672509`)
- Helper `doAccept_round'` / `doStore_round'` (commit `b767306`)

### Phase 3 — Minimal AcceptInv extract

- `network_acceptedBlockExists_trace` (commit `0feb0a3`)

### Phase 4 — Trace-level helpers (4 more)

- `network_find_advance_step` (commit `45af3da`)
- `network_hasProposedFor_monotone` +
  `network_proposed_for_lt_currentRound` (commit `68efb5a`)
- `network_all_honest_eventually_at_round` (commit `4d33235`)

### Phase 5 — §5 main theorems on `networkTrace`

- L1, L2 (commit `0c97a86`)
- T1 (commit `345de95`)
- T3 (commit `5bcbfcc`)
- T2, T4, isBlockSynchronizer (commit `bd67b42`)

### Phase 6 — Cleanup

- Deleted `belugaTrace` §5 wrappers + `NetworkBelugaCoherence`
  axiom + `belugaTrace_schedulerFairness` derived corollary
  (commit `27d0fe5`, removes ~830 lines).
