# 2026-04-26 — Phase E: structural lemmas + headline theorem stated (intermediate sorries)

Per the user's relaxation ("you can commit sorries in partial proofs
of this task with the goal to have no sorries in the task at the
end"), this commit lands Phase E.2–E.4 *as statements* of the
theorems, with intermediate sorries marking proof obligations.

## What changed

`Beluga/Network/Fairness.lean` now states:

### Phase E.2

- **`NetworkState.deliverPending_preserves_base_validators`** —
  proved (`base.validators` is unchanged by delivery).
- **`networkTryActFor_preserves_roundEntry_bound`** — stated;
  intermediate sorry. The structural argument (case-on-branch,
  use `updateValidator_getValidator_eq/_ne` and
  `doPropose_getValidator` from `Beluga/Theorems.lean`) requires
  factoring those helpers into a shared upstream module to avoid
  the circular import. Queued.
- **`roundEntryTime_le_currentTime`** — trace-level invariant.
  Zero case is mostly proved (one sub-sorry on the `init`
  validator-list bookkeeping); `succ` case sorries pending the
  step-lemma above.

### Phase E.3

- **`timeout_fires_past_4delta`** — proved (one-line, direct from
  the `timeoutFired` def).

### Phase E.4

- **`ActionScheduling`** — paper §4.2 + finding F-1 primitive.
  Defined.
- **`schedulerFairness_holds`** — stated. Bound is `5Δ` (timeout
  branch + Δ scheduling latency). Proof body sorry; outline given
  in the docstring.

## Sorries inventory

`Beluga/Network/Fairness.lean` has **4 sorries**:

1. `networkTryActFor_preserves_roundEntry_bound` — branch-by-branch
   case analysis; needs `updateValidator_getValidator_*` helpers
   in scope. Move helpers from `Beluga/Theorems.lean` to a shared
   upstream module (`Beluga/Protocol.lean` or a new
   `Beluga/StateUpdates.lean`).
2. `roundEntryTime_le_currentTime` zero case — bookkeeping on
   `init`'s validator-list construction. Show every validator in
   `(BelugaState.init system).validators` has the default
   `BelugaValidator` (specifically `roundEntryTime = 0`).
3. `roundEntryTime_le_currentTime` succ case — uses (1).
4. `schedulerFairness_holds` — main derivation; uses (3) +
   `ActionScheduling` + `timeout_fires_past_4delta`.

These four are the "structural plumbing" sorries; once (1) is
discharged, (2)–(4) follow with relatively short proofs.

`Beluga/Theorems.lean` is unchanged this commit — Phase F migration
follows once Phase E sorries close.

## Build state

`lake build` clean. Beluga/Theorems.lean: still 0 sorries. The 4
sorries are isolated to `Beluga/Network/Fairness.lean`.

## Phase F preview

The migration plan for Theorems.lean:

1. The §5 wrappers currently take `SchedulerFairness system time`.
2. Replace with `NetworkDelivery system time + ActionScheduling system time`.
3. Internally derive `SchedulerFairness` for `networkTrace` via
   `schedulerFairness_holds`.
4. Re-prove §5 main theorems against `networkTrace` (vs the
   current `belugaTrace`). This is the bulk of Phase F:
   - `find_advance_step`, `round_intermediate_value`,
     `all_honest_eventually_at_round`, `step_advance_inversion`
     and friends need `networkTrace`-aware versions.
   - The trace invariants (BlockInv, AcceptInv, AdmissionWellFormed)
     need to be re-established for `networkTrace`'s base evolution
     under `networkTryActFor` (which has the new ImPoA accept rule
     and timeout branch).

Estimated: ~1500–2000 lines of additional proof. 2–3 focused
sessions.

## Architectural decision pending

The post-Phase F end state has two traces (`belugaTrace` and
`networkTrace`) with parallel theorem developments. Cleaner
options to consider:

- **Option A**: deprecate `belugaTrace`; only `networkTrace` is
  paper-faithful and its theorems are the canonical §5 results.
  The existing `belugaTrace`-based theorems become historical
  scaffolding.
- **Option B**: keep both, prove a refinement: `belugaTrace`
  represents an "all-deliveries-are-immediate, no-Byzantine" run
  of `networkTrace`. The §5 theorems then transfer.
- **Option C**: replace `tryActFor` and `belugaTrace` in-place
  with the network-aware versions. Migrates everything at once.

Option A is the cleanest but requires the full re-proof effort.
Option B preserves backward compatibility. Option C is the most
invasive.
