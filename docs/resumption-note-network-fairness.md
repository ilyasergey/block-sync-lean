# Resumption note — paper-faithful fairness derivation

> **Audience.** A future Claude session picking up the task of
> deriving `SchedulerFairness` from paper primitives and migrating
> the §5 theorems to use it. The user's standing instruction is
> "no sorries at the end of this task" with intermediate sorries
> permitted while the work is in progress. The user prefers
> hand-proofs over Aristotle delegation for this work.
>
> **Read order**: this doc → relevant parts of
> [`plan-derive-fairness-from-primitives.md`](plan-derive-fairness-from-primitives.md) →
> the actual code in `BlockSynchroniser/Beluga/Network/`.

## TL;DR — what's done, what's pending

**Done** (build clean, no sorries in old code):

- Phases A–D: `BelugaValidator.roundEntryTime`; `NetworkState`
  with `inboxes`/`inflight`/`currentTime`; `deliverPending`;
  `networkTryActFor` with `T_rd = 4Δ` timeout branch and
  ImPoA-aware accept rule; `networkStep`; `networkTrace`;
  `SystemState NetworkState` instance.
- Phase E.1 + E.2 partial: 6 structural theorems proved
  (currentTime tracking, deliverPending preserving fields,
  branch-currentTime preservation), plus the zero case of
  `roundEntryTime_le_currentTime`.
- `timeout_fires_past_4delta` proved (one-line).
- `ActionScheduling` axiom defined.
- `schedulerFairness_holds` stated (5Δ bound).

**Pending** (3 sorries in `Beluga/Network/Fairness.lean`, lines
293, 356, 437):

1. `networkTryActFor_preserves_roundEntry_bound` (line 293) —
   the case-analysis on the four `networkTryActFor` branches.
   This is the **critical blocker**: once it's done, the rest
   of Phase E falls out.
2. `roundEntryTime_le_currentTime` succ case (line 356) —
   one-step IH application using (1).
3. `schedulerFairness_holds` (line 437) — main derivation.

**Phase F (Theorems.lean migration)**: not started.

## Where we are in the file

`BlockSynchroniser/Beluga/Network/Fairness.lean`:

- Lines 1–80: imports + namespace.
- Lines 82–140: **State-update helpers** — `updateValidator_getValidator_ne'`,
  `updateValidator_getValidator_eq'`, `doPropose_getValidator'`,
  `getValidator_emittedOperations_irrelevant'`. These are
  *duplicates* of the helpers in `Beluga/Theorems.lean`, copied
  here to avoid a circular import once Phase F migrates
  `Theorems.lean` to depend on `Network/Fairness.lean`. The proofs
  are identical; you can refactor by moving the originals to
  `Beluga/Protocol.lean` and removing this duplicate block.
- Lines 142–157: `NetworkDelivery` definition (the paper §2
  primitive — `Δ`-bounded honest-honest delivery).
- Lines 159–195: `RoundEntryTimeBounded`, `CurrentTimeTracksTime`,
  `TimeoutFiresPast4Delta` — *definitions* (some now subsumed by
  the proved theorems below).
- Lines 197–270: **Foundation theorems** (proved):
  - `NetworkState.deliverPending_preserves_currentTime`
  - `networkTryActFor_preserves_currentTime`
  - `networkStep_currentTime`
  - `currentTime_tracks_time`
  - `NetworkState.deliverPending_preserves_base_validators`
- Lines 273–293: `networkTryActFor_preserves_roundEntry_bound`
  with sorry. **PRIMARY TARGET.**
- Lines 295–356: `roundEntryTime_le_currentTime` — zero case
  proved; succ case is sorry.
- Lines 358–377: `timeout_fires_past_4delta` proved.
- Lines 379–410: `ActionScheduling` definition.
- Lines 412–437: `schedulerFairness_holds` with sorry.

## How to discharge the 3 sorries

### Sorry 1 (line 293): `networkTryActFor_preserves_roundEntry_bound`

**The shape.** Given `networkTryActFor system s vid_a bv_a = some s'`,
show that for every `(vid, bv)` with `s'.base.getValidator vid =
some bv`, `bv.roundEntryTime ≤ s'.currentTime`.

**Strategy.** Branch-by-branch case analysis matching
`networkTryActFor`'s four branches.

**Branch 1: propose** (`!hasProposedFor s vid_a r = true`).
Easy. `s'.base = doPropose system s.base vid_a r`. Use
`doPropose_getValidator'` to reduce to `s.base.getValidator vid =
some bv`, apply `h_inv`. Already mostly written in the previous
attempt; the `injection`/`rw [← h_eq]` plumbing works once you
get the `show` right.

**Branch 2: accept** (find?-of-`canAcceptBlock` returns `some B_acc`).
`s'.base = doAccept s.base vid_a B_acc`. Sub-cases:
- `vid = vid_a`: extract the original `bv₀` at vid (uses the
  fact that `updateValidator` preserves the *existence* of
  `getValidator vid = some _`, even though the value changes).
  Then `bv = { bv₀ with acceptedBlocks := ... }`, so
  `bv.roundEntryTime = bv₀.roundEntryTime`. Apply `h_inv` to bv₀.
- `vid ≠ vid_a`: use `updateValidator_getValidator_ne'` to
  reduce to `s.base.getValidator vid = some bv`, apply `h_inv`.

**Branch 3: store**. Same shape as accept.

**Branch 4: advance**. The actor's bv becomes `{ bv_a with
currentRound := r+1, roundEntryTime := s.currentTime }` (so
roundEntryTime = currentTime, easy). Non-actor validators are
unchanged.

**Where the previous attempt got stuck.** The `find?` ∘ `map`
expression in branches 2/3/4 made `Option.map_eq_some_iff` not
unify cleanly. Two fixes that should work:

(a) **Use the dedicated helpers**: don't `unfold updateValidator`
    or `unfold BelugaState.getValidator`. Stay at the level of
    `updateValidator_getValidator_eq'` / `_ne'`. The proofs
    `updateValidator_getValidator_eq'` already does the unfolding
    internally.

(b) For the actor sub-case in branches 2/3, the original `bv₀` at
    vid_a comes "from where"? It is **the bv_a passed to networkTryActFor**.
    Look at how the original networkTryActFor was called: `findSome?`
    over `s.base.validators`, and `(vid_a, bv_a)` is the matching
    pair. This means `s.base.getValidator vid_a = some bv_a`.
    There's a lemma to extract this from `findSome?_eq_some_iff` —
    look at how `step_advance_inversion` in `Beluga/Theorems.lean`
    handles the same situation.

**Suggested concrete approach**: pattern your proof after
`step_advance_inversion` (in `Beluga/Theorems.lean`, lines ~679–812).
That theorem case-analyzes `tryActFor`'s four branches and uses
exactly the same helpers; the `networkTryActFor` case-analysis
is structurally identical, just with more outer wrapping (the
`{ s with base := ... }` instead of bare `BelugaState`). Translate
each branch.

**Estimated effort**: ~150 lines of proof, 2–3 hours hand-coding.

### Sorry 2 (line 356): `roundEntryTime_le_currentTime` succ case

Once Sorry 1 is done, this is straightforward:
1. State `(networkTrace system time (k+1))` =
   `networkStep system (networkTrace system time k) (time (k+1))`.
2. Unfold `networkStep`: advance `currentTime`, deliverPending
   (preserves both `currentTime` and `base.validators`), then
   `findSome?` of `networkTryActFor`.
3. Case-split on `findSome?` result:
   - `none`: state's `getValidator` returns the same as
     `s_advanced.deliverPending.base.getValidator`. The IH at
     `k` plus time monotonicity gives the bound.
   - `some s'`: apply `networkTryActFor_preserves_roundEntry_bound`
     (the just-proved Sorry 1) with `h_inv` from the IH.

**Estimated effort**: ~50 lines, 1 hour.

### Sorry 3 (line 437): `schedulerFairness_holds`

The argument:
1. Take an honest `vid_h` at round `r` at trace step `k`. By
   `roundEntryTime_le_currentTime` (Sorry 2 just proved),
   `bv_h.roundEntryTime ≤ time k`.
2. Use `Unbounded` (from `time.WellFormed`) to find `k_t` with
   `time k_t ≥ time k + 4Δ`. Note `bv_h.roundEntryTime + 4Δ ≤
   time k + 4Δ ≤ time k_t`, so `timeout_fires_past_4delta`
   applies at `k_t`.
3. By `ActionScheduling`, vid_h is selected within Δ further
   wall-clock; total ≤ time k + 5Δ.
4. When vid_h is selected with timeout fired, the advance branch
   activates. So vid_h reaches round ≥ r+1 within 5Δ.
5. Iterate over all honest validators (each completes its own
   5Δ window; lockstep follows from time monotonicity).

**Note on the `5Δ` vs paper's `3Δ`**: our derivation goes via the
timeout safety net, which costs `4Δ + Δ = 5Δ`. The paper's
optimistic `3Δ` bound requires modeling ImPoA-pull synchronization
in detail (post-GST, honest blocks reach 2f+1-quorum status within
2Δ via direct delivery + ImPoA, before the timeout fires). That
refinement is future work; for now `5Δ` is the bound.

**Estimated effort**: ~250 lines, half-day.

## Phase F — Theorems.lean migration

Once the 3 sorries above close, Phase F migrates the §5 theorems to
take `NetworkDelivery + ActionScheduling` instead of
`SchedulerFairness`. The key architectural decision (deferred):

### Architectural options

Option A (most paper-faithful): re-prove §5 against `networkTrace`.
Each helper (`find_advance_step`, `round_intermediate_value`,
`all_honest_eventually_at_round`, `step_advance_inversion`,
`step_advance_implies_*`, `proposed_for_lt_currentRound`,
`belugaTrace_validators_nodup`, `accepted_at_advance`,
`block_parents_in_pool`, etc.) needs a network-trace version. The
trace invariants (`BlockInv`, `AcceptInv`, `AdmissionWellFormed`)
need to hold for `networkTrace`'s base evolution under
`networkTryActFor`'s richer accept rule (ImPoA) and richer advance
rule (timeout). Estimated: ~1500–2000 lines.

Option B (compatibility-preserving): prove a refinement theorem —
under "ideal" conditions (no Byzantine senders, all deliveries
immediate, no timeouts), `networkTrace` behaves like `belugaTrace`.
Then `SchedulerFairness for networkTrace` transfers to
`SchedulerFairness for belugaTrace`, and the existing §5 proofs
work as-is (just take the new primitives + the refinement
condition). Estimated: ~500 lines.

Option C (replace): swap `belugaTrace`/`step` for `networkTrace`/
`networkStep` in `Beluga/Protocol.lean` itself. All downstream
files migrate automatically. The simplest end-state but the
biggest one-shot change. Estimated: ~2000 lines.

**Recommendation**: Option A. It is the most faithful and the
cleanest end state. Option B's "refinement" is a brittle
abstraction; Option C creates a flag-day migration that is harder
to review.

### Concrete Phase F plan (Option A)

1. Create `Beluga/Network/Theorems.lean` mirroring `Beluga/Theorems.lean`
   but stating each result against `networkTrace`.
2. Port helper lemmas one at a time:
   `belugaTrace_validators_nodup` → `networkTrace_validators_nodup`,
   etc. Each port is a one-paragraph rewrite of the existing
   proof, swapping `step` for `networkStep` and `belugaTrace` for
   `networkTrace`.
3. Re-state and re-prove `step_advance_inversion` for
   `networkTryActFor`. The advance branch now has a disjunctive
   gate (`allProposedFor ∨ timeoutFired`); both sub-cases need
   to be handled.
4. The trace invariants (`BlockInv`, `AcceptInv`, etc.) need
   `networkTrace` versions. The ImPoA-aware accept rule may
   require relaxing `AcceptInv.acceptedParents` (vid accepts B
   no longer implies vid accepts all parents — only that they
   are *available*).
5. Re-state and re-prove §5 main theorems. Most proofs port
   line-by-line; the L1/L2 "fairness invocation" steps now go
   through `schedulerFairness_holds` instead of taking
   `SchedulerFairness` as a parameter.
6. Once all of `Beluga/Network/Theorems.lean` is ported and
   sorry-free, deprecate `Beluga/Theorems.lean` (or remove it).

## What to NOT touch

- `BlockSynchroniser/Beluga/Theorems.lean` — currently proven,
  0 sorries. Don't break this while migrating; you may need
  references to its lemmas during Phase F's port.
- `BlockSynchroniser/Beluga/Protocol.lean` — the existing
  `step`/`belugaTrace` should remain unchanged. `Protocol.lean`
  is the dependency root for everything; modifying it triggers a
  rebuild of the entire `Beluga/` tree.
- The state-update helpers in `Network/Fairness.lean` are
  duplicates; you may eventually move them to
  `Beluga/Protocol.lean` (their natural home), but only after
  Phase F's port is done.

## Build sanity checks at every commit

After every edit:
```
lake build BlockSynchroniser.Beluga.Network.Fairness
```
Then full:
```
lake build
```

Confirm no NEW sorries were introduced (the existing 3 in
`Network/Fairness.lean` and 1 in `Mysticeti/Liveness.lean` are
the baseline). Use:
```
grep -rn "sorry" BlockSynchroniser/ | grep -v "^Binary" | wc -l
```

## Conventions to honor

- `CLAUDE.md` "no `sorry` in comments/docstrings" rule. The word
  `sorry` may appear *only* as a tactic in `:= by sorry` proof
  obligations. In prose, use "stub", "pending", "queued",
  "incomplete", "unproved", "left open", "deferred". The
  resumption note above intentionally ignores this for clarity;
  before final commit, sweep the new docstrings/comments for
  any literal "sorry" mentions and rewrite.
- Update `formalization.md` and add a `changelogs/` entry per
  the project rules in `CLAUDE.md`.
- Commit per phase, not all at once. Each commit's message:
  what changed + why + build state + sorries-count.

## User's standing rules for this work

- **No sorries at the end** of the task (intermediate OK).
- **No Aristotle** for this work — all hand-proven.
- The user values paper-faithfulness highly; if you need to weaken
  a bound or change a primitive, document the trade-off in
  `mechanization-findings.md`.
- The user explicitly authorized "do as you think is better".
  Make decisions; don't ask routine questions. Big architectural
  choices (e.g., Option A vs B vs C above) — flag, decide, document.

## Final check before declaring "done"

1. `lake build` clean.
2. `grep -rn "sorry" BlockSynchroniser/Beluga/` returns nothing
   (or only legitimate ":= by sorry" if you've intentionally left
   one for the *next* phase; the user explicitly wants none for
   this task).
3. `Beluga/Theorems.lean` either:
   (a) takes `NetworkDelivery + ActionScheduling` instead of
       `SchedulerFairness`, OR
   (b) is migrated to `Beluga/Network/Theorems.lean` and the old
       file is deprecated/removed.
4. `formalization.md` updated; new `changelogs/` entry; possibly
   `mechanization-findings.md` updated with the F-1 resolution
   note ("F-1 resolved by Phase E.4 — `schedulerFairness_holds`
   theorem in `Network/Fairness.lean`").
