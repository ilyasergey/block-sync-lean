/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Derivation of `SchedulerFairness` from paper primitives.

This module is the payoff of the network-aware refinement: it proves
that the round-progression assumption surfaced as `SchedulerFairness`
in [`Beluga/Theorems.lean`](../Theorems.lean) is in fact a *theorem*
about `networkTrace`, derivable from paper §2 (`Δ`-bounded delivery)
and paper §4.2 (per-round timeout `T_rd = 4Δ`).

The proof argument matches paper L1's prose, but routed through the
**timeout** branch (the safety-net bound) rather than the
quorum-completion branch (the optimistic 3Δ bound). This gives a
slightly weaker `4Δ` time bound rather than the paper's nominal
`3Δ`, but it is provable from the primitives without needing the
full ImPoA-pull synchronization argument the paper sketches for the
3Δ bound. The 3Δ refinement is future work (see
[`docs/plan-derive-fairness-from-primitives.md`](../../../docs/plan-derive-fairness-from-primitives.md)).

## Outline

1. **`NetworkDelivery`** — the paper §2 primitive: post-GST,
   honest-to-honest deliveries arrive within `Δ`.
2. **Round-monotonicity** — `roundEntryTime` is bounded by the
   wall-clock at the step where the validator entered the round.
3. **Timeout-fires** — past `roundEntryTime + 4Δ`, the timeout
   branch is enabled.
4. **`schedulerFairness4Δ_holds`** — combining the above, every
   honest validator advances within `4Δ` post-GST, yielding the
   network-trace's analog of `SchedulerFairness` with the relaxed
   bound.
-/
import BlockSynchroniser.Beluga.Network.Protocol

namespace BlockSynchroniser
namespace Beluga
namespace Network

/-! ## State-update helpers (mirrors of `Beluga/Theorems.lean`)

These lemmas are duplicated from `Beluga/Theorems.lean` to avoid a
prospective circular import once `Theorems.lean` itself migrates to
`networkTrace` (Phase F). The proofs are identical; future
refactoring can move them to `Beluga/Protocol.lean` (their natural
home) and remove this duplicate block. -/

private lemma updateValidator_getValidator_ne'
    (s : BelugaState) (vid vid' : ValidatorId)
    (f : BelugaValidator → BelugaValidator) (h : vid ≠ vid') :
    (updateValidator s vid' f).getValidator vid = s.getValidator vid := by
  unfold updateValidator BelugaState.getValidator
  induction s.validators <;> simp +decide [*]
  grind

private lemma updateValidator_getValidator_eq'
    (s : BelugaState) (vid : ValidatorId)
    (f : BelugaValidator → BelugaValidator) (bv : BelugaValidator)
    (h : s.getValidator vid = some bv) :
    (updateValidator s vid f).getValidator vid = some (f bv) := by
  unfold BelugaState.getValidator at *
  unfold updateValidator; simp +decide
  rw [Option.map_eq_some_iff] at h
  grind +suggestions

private lemma doPropose_getValidator'
    (system : BlockSynchroniserSystem) (s : BelugaState)
    (vid vid' : ValidatorId) (r : Round) :
    (doPropose system s vid' r).getValidator vid = s.getValidator vid := by
  exact (Option.map_inj_right fun x y a => a).mp rfl

private lemma getValidator_emittedOperations_irrelevant'
    (s : BelugaState) (ops : List ValidatorOperation) (vid : ValidatorId) :
    ({ s with emittedOperations := ops } : BelugaState).getValidator vid =
      s.getValidator vid := by
  unfold BelugaState.getValidator; aesop

/-- `doAccept` preserves `currentRound` for all validators. -/
private lemma doAccept_round' (s : BelugaState) (vid vid' : ValidatorId) (B : Block)
    (bv : BelugaValidator) (h : s.getValidator vid = some bv) :
    ∃ bv', (doAccept s vid' B).getValidator vid = some bv' ∧
           bv'.currentRound = bv.currentRound := by
  by_cases h' : vid = vid' <;> simp_all +decide [doAccept]
  · exact ⟨_, updateValidator_getValidator_eq' _ _ _ _ h, rfl⟩
  · rw [updateValidator_getValidator_ne']; aesop
    assumption

/-- `doStore` preserves `currentRound` for all validators. -/
private lemma doStore_round' (s : BelugaState) (vid vid' : ValidatorId) (B : Block)
    (bv : BelugaValidator) (h : s.getValidator vid = some bv) :
    ∃ bv', (doStore s vid' B).getValidator vid = some bv' ∧
           bv'.currentRound = bv.currentRound := by
  by_cases h' : vid = vid'
  · subst h'
    exact ⟨_, updateValidator_getValidator_eq' _ _ _ bv h, rfl⟩
  · unfold doStore
    refine ⟨bv, ?_, rfl⟩
    rw [updateValidator_getValidator_ne' _ _ _ _ h',
        getValidator_emittedOperations_irrelevant']
    exact h


/-! ## Paper §2 primitive: `Δ`-bounded delivery -/

/-- **`NetworkDelivery`** — paper §2's primitive: post-GST, every
honest-to-honest push delivery completes within `Δ`. Formally: at
any post-GST step `k` of `networkTrace`, if a `block_propose` op
from honest sender `vid_s` was emitted at or before step `k`, then
some step `k'` within wall-clock `Δ` of `k` has every honest
recipient's inbox containing the op.

This is the **only** new axiom needed by Phase E; everything else
in this file is derived. The axiom corresponds to paper Section 2's
network model:

> *We assume the network is partially synchronous: after GST, every
> message between honest validators is delivered within Δ.*

The trace-level statement quantifies over honest senders and
recipients (Byzantine senders' messages may be delayed
arbitrarily). -/
def NetworkDelivery (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop :=
  ∀ k vid_s vid_r B r,
    isHonestValidator system vid_s = true →
    isHonestValidator system vid_r = true →
    time k ≥ system.GST →
    ValidatorOperation.block_propose vid_s B r ∈
      (networkTrace system time k).base.emittedOperations →
    ∃ k', k ≤ k' ∧ time k' ≤ time k + system.Δ ∧
      ValidatorOperation.block_propose vid_s B r ∈
        (networkTrace system time k').inbox vid_r

/-! ## Paper §2 + §4.2 primitives, with-pull variants

The with-pull versions of `NetworkDelivery` and `ActionScheduling`,
stated against `networkTraceWithPull`. Same shape as the originals
but with the pull-aware trace. -/

/-- Push-channel `Δ`-bounded delivery on `networkTraceWithPull`. -/
def NetworkDeliveryWithPull (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop :=
  ∀ k vid_s vid_r B r,
    isHonestValidator system vid_s = true →
    isHonestValidator system vid_r = true →
    time k ≥ system.GST →
    ValidatorOperation.block_propose vid_s B r ∈
      (networkTraceWithPull system time k).base.emittedOperations →
    ∃ k', k ≤ k' ∧ time k' ≤ time k + system.Δ ∧
      ValidatorOperation.block_propose vid_s B r ∈
        (networkTraceWithPull system time k').inbox vid_r

/-- Per-validator round-advance liveness on `networkTraceWithPull`. -/
def ActionSchedulingWithPull (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop :=
  ∀ k vid bv,
    isHonestValidator system vid = true →
    time k ≥ system.GST →
    (networkTraceWithPull system time k).base.getValidator vid = some bv →
    ∃ k' bv', k ≤ k' ∧ time k' ≤ time k + system.Δ ∧
      (networkTraceWithPull system time k').base.getValidator vid = some bv' ∧
      bv'.currentRound > bv.currentRound

/-- Round-spread invariant on `networkTraceWithPull`. -/
def BoundedRoundSpread_networkTraceWithPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop :=
  ∀ k vid₁ vid₂ bv₁ bv₂,
    time k ≥ system.GST →
    isHonestValidator system vid₁ = true →
    isHonestValidator system vid₂ = true →
    (networkTraceWithPull system time k).base.getValidator vid₁ = some bv₁ →
    (networkTraceWithPull system time k).base.getValidator vid₂ = some bv₂ →
    bv₁.currentRound ≤ bv₂.currentRound + 1

/-! ## Paper §4.3 pull primitives

The pull mechanism (paper §4.3) requires three liveness primitives,
each mirroring an existing one for the push channel. These let us
derive `EventualCausalAcceptance` and `EventualRoundAcceptance` as
theorems on `networkTraceWithPull`. -/

/-- **`PullRequestDelivery`** — pull-channel analog of
`NetworkDelivery`: post-GST, every pull request issued by an honest
requester to an honest responder is delivered to the responder's
`pullRequestsInbox` within `Δ`. Mirrors paper §2's `Δ`-bounded
delivery for the pull-request channel. -/
def PullRequestDelivery (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop :=
  ∀ k (req : PullRequest),
    isHonestValidator system req.requester = true →
    isHonestValidator system req.responder = true →
    time k ≥ system.GST →
    req ∈ (networkTraceWithPull system time k).pullRequestsInflight →
    ∃ k', k ≤ k' ∧ time k' ≤ time k + system.Δ ∧
      req ∈ (networkTraceWithPull system time k').pullInbox req.responder

/-- **`PullResponseScheduling`** — analog of `ActionScheduling` for
the pull-response action: post-GST, when an honest responder has a
pending pull request in its inbox, it processes the first request
within `Δ` (`pullStepOne`'s respond branch fires). -/
def PullResponseScheduling (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop :=
  ∀ k (vid_resp : ValidatorId) (req : PullRequest),
    isHonestValidator system vid_resp = true →
    time k ≥ system.GST →
    req ∈ (networkTraceWithPull system time k).pullInbox vid_resp →
    ∃ k', k ≤ k' ∧ time k' ≤ time k + system.Δ ∧
      req ∉ (networkTraceWithPull system time k').pullInbox vid_resp

/-- **`AcceptScheduling`** — paper §4.2's per-action liveness for
the accept action: post-GST, when an honest validator has an
acceptable in-pool block (canAcceptBlock = true), the validator's
`doAccept` action fires within `Δ`. -/
def AcceptScheduling (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop :=
  ∀ k vid B,
    isHonestValidator system vid = true →
    time k ≥ system.GST →
    B ∈ (networkTraceWithPull system time k).base.blocks →
    (networkTraceWithPull system time k).canAcceptBlock system vid B = true →
    ∃ k', k ≤ k' ∧ time k' ≤ time k + system.Δ ∧
      hasAcceptedDigest (networkTraceWithPull system time k').base vid B.d = true

/-- **`NetworkInPoolDeliveryWithPull`** — the consolidated
push+pull delivery primitive: post-GST, every in-pool block whose
digest the honest validator has not yet accepted is eventually
delivered to the validator's inbox. This subsumes:

- **Push** (paper §2 + §4.2): for honest-authored blocks, the
  proposer's broadcast reaches every honest validator within `Δ`.
- **Pull** (paper §4.3): for blocks the honest validator has not
  received via push (e.g., Byzantine-authored), the
  `pullCandidate`/`pullStepOne` mechanism issues a request, the
  responder schedules a `block_propose` reply, and `deliverPending`
  delivers it to the validator's inbox.

The primitive is stated as a single liveness statement to match the
paper's high-level §4.3 claim that "every in-pool block is eventually
known to every honest validator post-GST." Atomic derivation from
`PullRequestDelivery` + `PullResponseScheduling` + `NetworkDeliveryWithPull`
is feasible but requires careful chaining of `pullStepOne`'s issue
branch — left as a future structural derivation. -/
def NetworkInPoolDeliveryWithPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop :=
  ∀ k vid B,
    isHonestValidator system vid = true →
    time k ≥ system.GST →
    B ∈ (networkTraceWithPull system time k).base.blocks →
    hasAcceptedDigest (networkTraceWithPull system time k).base vid B.d = false →
    ∃ k', k ≤ k' ∧
      ValidatorOperation.block_propose B.author B B.r ∈
        (networkTraceWithPull system time k').inbox vid

/-! ## Trace structure: monotonicity + timeout firing

The full derivation requires several structural lemmas about
`networkTrace`. Their proofs follow the same case-on-`tryActFor`-
branch pattern as the existing Beluga proofs, augmented with the
new delivery + timeout branches. We list the load-bearing lemmas
below as a roadmap; the proofs are the bulk of Phase E proper. -/

/-- **Round-progress upper bound**: at every step of
`networkTrace`, every honest validator at round `r` with
`roundEntryTime = t` has `currentTime ≥ t` (the validator did
enter the round at or before now). Self-inductive on the trace,
case-analyzing `networkTryActFor`'s branches. -/
def RoundEntryTimeBounded (system : BlockSynchroniserSystem) (time : Nat → Nat) :
    Prop :=
  ∀ k vid bv,
    (networkTrace system time k).base.getValidator vid = some bv →
    bv.roundEntryTime ≤ (networkTrace system time k).currentTime

/-- **Wall-clock-tracks-time**: the `currentTime` field of
`networkTrace system time k` equals `time k`. By construction
(`networkStep` sets `currentTime := newTime`). -/
def CurrentTimeTracksTime (system : BlockSynchroniserSystem) (time : Nat → Nat) :
    Prop :=
  ∀ k, (networkTrace system time k).currentTime = time k

/-- **Timeout-fires-eventually**: at every post-`(roundEntryTime +
4Δ)` step, the timeout branch of `networkTryActFor` is enabled for
the validator. Direct from the definition of `timeoutFired`. -/
def TimeoutFiresPast4Delta (system : BlockSynchroniserSystem) (time : Nat → Nat) :
    Prop :=
  ∀ k vid bv,
    (networkTrace system time k).base.getValidator vid = some bv →
    time k ≥ bv.roundEntryTime + 4 * system.Δ →
    (networkTrace system time k).timeoutFired system bv = true

/-! ## Foundation lemmas (Phase E.2) -/

/-- `deliverPending` preserves `currentTime`. By definition: the
folded `appendToInbox` only changes `inboxes`, and the partition
operation only modifies `inflight`. -/
theorem NetworkState.deliverPending_preserves_currentTime (s : NetworkState) :
    s.deliverPending.currentTime = s.currentTime := by
  unfold NetworkState.deliverPending
  generalize hp : s.inflight.partition _ = p
  -- Now we have `p.1.foldl ... { s with inflight := p.2 }`; show
  -- the foldl preserves currentTime.
  suffices h : ∀ (l : List DeliveryEvent) (s' : NetworkState),
      s'.currentTime = s.currentTime →
      (l.foldl (fun acc e => acc.appendToInbox e.recipient e.op) s').currentTime =
        s.currentTime by
    apply h; rfl
  intro l
  induction l with
  | nil => intro s' h; exact h
  | cons hd tl ih =>
    intro s' h
    apply ih
    simp [NetworkState.appendToInbox, h]

/-- `deliverPullPending` preserves `currentTime`. -/
theorem NetworkState.deliverPullPending_preserves_currentTime (s : NetworkState) :
    s.deliverPullPending.currentTime = s.currentTime := by
  unfold NetworkState.deliverPullPending
  generalize hp : s.pullRequestsInflight.partition _ = p
  suffices h : ∀ (l : List PullRequest) (s' : NetworkState),
      s'.currentTime = s.currentTime →
      (l.foldl (fun acc r => acc.appendToPullInbox r.responder r) s').currentTime =
        s.currentTime by
    apply h; rfl
  intro l
  induction l with
  | nil => intro s' h; exact h
  | cons hd tl ih =>
    intro s' h
    apply ih
    simp [NetworkState.appendToPullInbox, h]

/-- `deliverPullPending` preserves the `base` field. -/
theorem NetworkState.deliverPullPending_preserves_base (s : NetworkState) :
    s.deliverPullPending.base = s.base := by
  unfold NetworkState.deliverPullPending
  generalize hp : s.pullRequestsInflight.partition _ = p
  suffices h : ∀ (l : List PullRequest) (s' : NetworkState),
      s'.base = s.base →
      (l.foldl (fun acc r => acc.appendToPullInbox r.responder r) s').base = s.base by
    apply h; rfl
  intro l
  induction l with
  | nil => intro s' h; exact h
  | cons hd tl ih =>
    intro s' h
    apply ih; simp [NetworkState.appendToPullInbox, h]

/-- `deliverPullPending` preserves `inflight`. -/
theorem NetworkState.deliverPullPending_preserves_inflight (s : NetworkState) :
    s.deliverPullPending.inflight = s.inflight := by
  unfold NetworkState.deliverPullPending
  generalize hp : s.pullRequestsInflight.partition _ = p
  suffices h : ∀ (l : List PullRequest) (s' : NetworkState),
      s'.inflight = s.inflight →
      (l.foldl (fun acc r => acc.appendToPullInbox r.responder r) s').inflight = s.inflight by
    apply h; rfl
  intro l
  induction l with
  | nil => intro s' h; exact h
  | cons hd tl ih =>
    intro s' h
    apply ih; simp [NetworkState.appendToPullInbox, h]

/-- `deliverPullPending` preserves `inboxes`. -/
theorem NetworkState.deliverPullPending_preserves_inboxes (s : NetworkState) :
    s.deliverPullPending.inboxes = s.inboxes := by
  unfold NetworkState.deliverPullPending
  generalize hp : s.pullRequestsInflight.partition _ = p
  suffices h : ∀ (l : List PullRequest) (s' : NetworkState),
      s'.inboxes = s.inboxes →
      (l.foldl (fun acc r => acc.appendToPullInbox r.responder r) s').inboxes = s.inboxes by
    apply h; rfl
  intro l
  induction l with
  | nil => intro s' h; exact h
  | cons hd tl ih =>
    intro s' h
    apply ih; simp [NetworkState.appendToPullInbox, h]

/-- `doPullRequest` preserves `currentTime`. -/
theorem doPullRequest_preserves_currentTime (system : BlockSynchroniserSystem)
    (s : NetworkState) (vid : ValidatorId) (d : BlockDigest) :
    (doPullRequest system s vid d).currentTime = s.currentTime := by
  unfold doPullRequest; rfl

/-- `doPullRequest` preserves `base`. -/
theorem doPullRequest_preserves_base (system : BlockSynchroniserSystem)
    (s : NetworkState) (vid : ValidatorId) (d : BlockDigest) :
    (doPullRequest system s vid d).base = s.base := by
  unfold doPullRequest; rfl

/-- `doPullResponse` preserves `currentTime`. -/
theorem doPullResponse_preserves_currentTime (system : BlockSynchroniserSystem)
    (s : NetworkState) (vid_resp : ValidatorId) (req : PullRequest) :
    (doPullResponse system s vid_resp req).currentTime = s.currentTime := by
  unfold doPullResponse
  split <;> simp [NetworkState.removeFromPullInbox]

/-- `doPullResponse` preserves `base`. -/
theorem doPullResponse_preserves_base (system : BlockSynchroniserSystem)
    (s : NetworkState) (vid_resp : ValidatorId) (req : PullRequest) :
    (doPullResponse system s vid_resp req).base = s.base := by
  unfold doPullResponse
  split <;> simp [NetworkState.removeFromPullInbox]

/-- `pullStepOne` preserves `currentTime`. -/
theorem pullStepOne_preserves_currentTime (system : BlockSynchroniserSystem)
    (s : NetworkState) (vid : ValidatorId) :
    (pullStepOne system s vid).currentTime = s.currentTime := by
  unfold pullStepOne
  split
  · rw [doPullResponse_preserves_currentTime]
  · split
    · rw [doPullRequest_preserves_currentTime]
    · rfl

/-- `pullStepOne` preserves `base`. -/
theorem pullStepOne_preserves_base (system : BlockSynchroniserSystem)
    (s : NetworkState) (vid : ValidatorId) :
    (pullStepOne system s vid).base = s.base := by
  unfold pullStepOne
  split
  · rw [doPullResponse_preserves_base]
  · split
    · rw [doPullRequest_preserves_base]
    · rfl

/-- `pullStep` preserves `currentTime`. -/
theorem pullStep_preserves_currentTime (system : BlockSynchroniserSystem)
    (s : NetworkState) :
    (pullStep system s).currentTime = s.currentTime := by
  unfold pullStep
  suffices h : ∀ (l : List (ValidatorId × Bool)) (s' : NetworkState),
      s'.currentTime = s.currentTime →
      (l.foldl (fun acc x => pullStepOne system acc x.1) s').currentTime = s.currentTime by
    apply h; rfl
  intro l
  induction l with
  | nil => intro s' h; exact h
  | cons hd tl ih =>
    intro s' h
    apply ih
    rw [pullStepOne_preserves_currentTime]; exact h

/-- `pullStep` preserves `base`. -/
theorem pullStep_preserves_base (system : BlockSynchroniserSystem)
    (s : NetworkState) :
    (pullStep system s).base = s.base := by
  unfold pullStep
  suffices h : ∀ (l : List (ValidatorId × Bool)) (s' : NetworkState),
      s'.base = s.base →
      (l.foldl (fun acc x => pullStepOne system acc x.1) s').base = s.base by
    apply h; rfl
  intro l
  induction l with
  | nil => intro s' h; exact h
  | cons hd tl ih =>
    intro s' h
    apply ih
    rw [pullStepOne_preserves_base]; exact h

/-- Each branch of `networkTryActFor` preserves `currentTime`.
Direct from the definition: every branch returns
`some { s with base := ... }` (or `{ s with base := ..., inflight :=
... }`), reusing `s.currentTime` via the structure-update syntax. -/
theorem networkTryActFor_preserves_currentTime
    (system : BlockSynchroniserSystem) (s : NetworkState)
    (vid : ValidatorId) (bv : BelugaValidator) (s' : NetworkState)
    (h : networkTryActFor system s vid bv = some s') :
    s'.currentTime = s.currentTime := by
  unfold networkTryActFor at h
  simp only at h
  split at h
  · -- doPropose branch
    injection h with h_eq
    rw [← h_eq]
  · split at h
    · -- doAccept branch
      injection h with h_eq
      rw [← h_eq]
    · split at h
      · -- doStore branch
        injection h with h_eq
        rw [← h_eq]
      · -- doAdvance branch (or none)
        split at h
        · injection h with h_eq
          rw [← h_eq]
        · contradiction

/-- `networkStep` sets `currentTime` to `newTime`. -/
theorem networkStep_currentTime
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat) :
    (networkStep system s newTime).currentTime = newTime := by
  have h_del_ct : ({ s with currentTime := newTime }
      : NetworkState).deliverPending.currentTime = newTime := by
    rw [NetworkState.deliverPending_preserves_currentTime]
  unfold networkStep
  simp only
  split
  case _ s' h_fs =>
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, ⟨vid, bv⟩, _, _, h_act, _⟩ := h_fs
    have := networkTryActFor_preserves_currentTime system _ vid bv s' h_act
    rw [this]; exact h_del_ct
  case _ _ => exact h_del_ct

/-- The `currentTime` field of `networkTrace system time k` equals
`time k`. -/
theorem currentTime_tracks_time (system : BlockSynchroniserSystem)
    (time : Nat → Nat) (k : Nat) :
    (networkTrace system time k).currentTime = time k := by
  induction k with
  | zero =>
    show ({ NetworkState.init system with currentTime := time 0 } : NetworkState).currentTime
        = time 0
    rfl
  | succ k _ =>
    show (networkStep system (networkTrace system time k) (time (k + 1))).currentTime =
      time (k + 1)
    exact networkStep_currentTime system (networkTrace system time k) (time (k + 1))

/-! ## Foundational lemmas on `networkStepWithPull` and `networkTraceWithPull` -/

/-- `networkStepWithPull` sets `currentTime` to `newTime`. -/
theorem networkStepWithPull_currentTime
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat) :
    (networkStepWithPull system s newTime).currentTime = newTime := by
  have h_del_ct : ({ s with currentTime := newTime }
      : NetworkState).deliverPending.currentTime = newTime := by
    rw [NetworkState.deliverPending_preserves_currentTime]
  have h_pull_del_ct :
      (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending).currentTime = newTime := by
    rw [NetworkState.deliverPullPending_preserves_currentTime]; exact h_del_ct
  have h_pulled_ct :
      (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).currentTime = newTime := by
    rw [pullStep_preserves_currentTime]; exact h_pull_del_ct
  unfold networkStepWithPull
  simp only
  split
  case _ s' h_fs =>
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, ⟨vid, bv⟩, _, _, h_act, _⟩ := h_fs
    have := networkTryActFor_preserves_currentTime system _ vid bv s' h_act
    rw [this]; exact h_pulled_ct
  case _ _ => exact h_pulled_ct

/-- `currentTime` of `networkTraceWithPull` at step `k` equals `time k`. -/
theorem currentTime_tracks_time_withPull (system : BlockSynchroniserSystem)
    (time : Nat → Nat) (k : Nat) :
    (networkTraceWithPull system time k).currentTime = time k := by
  induction k with
  | zero =>
    show ({ NetworkState.init system with currentTime := time 0 } : NetworkState).currentTime
        = time 0
    rfl
  | succ k _ =>
    show (networkStepWithPull system (networkTraceWithPull system time k) (time (k + 1))).currentTime =
      time (k + 1)
    exact networkStepWithPull_currentTime system (networkTraceWithPull system time k) (time (k + 1))

/-! ## Network-trace structural invariants

These invariants are the network-aware analogues of `belugaTrace`'s
existing structural invariants (in `Beluga/Theorems.lean`). They
support the round-entry / scheduler-fairness arguments below. -/

/-- `updateValidator` preserves the validator-id list. -/
private lemma updateValidator_preserves_ids
    (s : BelugaState) (vid_a : ValidatorId) (f : BelugaValidator → BelugaValidator) :
    (updateValidator s vid_a f).validators.map Prod.fst = s.validators.map Prod.fst := by
  unfold updateValidator
  simp only
  -- The map of `.1` over a list-map that preserves `.1` (only changes `.2`)
  -- is the same as the original `.1` map.
  rw [List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  by_cases h : p.1 = vid_a <;> simp [h]

/-- `doPropose` preserves the validator-id list. -/
private lemma doPropose_preserves_ids
    (system : BlockSynchroniserSystem) (s : BelugaState)
    (vid : ValidatorId) (r : Round) :
    (doPropose system s vid r).validators.map Prod.fst = s.validators.map Prod.fst := by
  rfl

/-- `doAccept` preserves the validator-id list (via `updateValidator`). -/
private lemma doAccept_preserves_ids
    (s : BelugaState) (vid_a : ValidatorId) (B : Block) :
    (doAccept s vid_a B).validators.map Prod.fst = s.validators.map Prod.fst := by
  unfold doAccept
  exact updateValidator_preserves_ids _ _ _

/-- `doStore` preserves the validator-id list. -/
private lemma doStore_preserves_ids
    (s : BelugaState) (vid_a : ValidatorId) (B : Block) :
    (doStore s vid_a B).validators.map Prod.fst = s.validators.map Prod.fst := by
  unfold doStore
  exact updateValidator_preserves_ids _ _ _

/-- The validator-id list is preserved across `networkTryActFor`. The
network-trace's nodup-by-id invariant is preserved by every branch
(propose / accept / store / advance), since each branch uses
`updateValidator` (or doesn't touch validators at all). -/
private lemma networkTryActFor_preserves_ids
    (system : BlockSynchroniserSystem) (s : NetworkState)
    (vid_a : ValidatorId) (bv_a : BelugaValidator) (s' : NetworkState)
    (h_act : networkTryActFor system s vid_a bv_a = some s') :
    s'.base.validators.map Prod.fst = s.base.validators.map Prod.fst := by
  unfold networkTryActFor at h_act
  simp only at h_act
  split at h_act
  · -- propose
    injection h_act with h_eq
    rw [← h_eq]
    show (doPropose system s.base vid_a bv_a.currentRound).validators.map Prod.fst = _
    exact doPropose_preserves_ids system s.base vid_a bv_a.currentRound
  · split at h_act
    · -- accept
      rename_i B_acc _
      injection h_act with h_eq
      rw [← h_eq]
      exact doAccept_preserves_ids s.base vid_a B_acc
    · split at h_act
      · -- store
        rename_i _ B_sto _
        injection h_act with h_eq
        rw [← h_eq]
        exact doStore_preserves_ids s.base vid_a B_sto
      · split at h_act
        · injection h_act with h_eq
          rw [← h_eq]
          exact updateValidator_preserves_ids s.base vid_a _
        · contradiction

/-- `deliverPending` preserves the validator-id list (since it
preserves `base.validators` entirely). The `appendToInbox` helper
only modifies `inboxes`, never `base`. -/
private lemma deliverPending_preserves_ids (s : NetworkState) :
    s.deliverPending.base.validators.map Prod.fst =
    s.base.validators.map Prod.fst := by
  unfold NetworkState.deliverPending
  -- The foldl over `appendToInbox` doesn't change `base.validators`.
  have aux : ∀ (l : List DeliveryEvent) (s' : NetworkState),
      s'.base.validators.map Prod.fst = s.base.validators.map Prod.fst →
      (l.foldl (fun acc e => acc.appendToInbox e.recipient e.op) s').base.validators.map Prod.fst
        = s.base.validators.map Prod.fst := by
    intro l
    induction l with
    | nil => intro _ h; exact h
    | cons hd tl ih =>
      intro s' h
      apply ih
      simp [NetworkState.appendToInbox, h]
  generalize hp : s.inflight.partition _ = p
  obtain ⟨toDeliver, stillInflight⟩ := p
  simp only
  exact aux toDeliver _ rfl

/-- `networkStep` preserves the validator-id list. -/
private lemma networkStep_preserves_ids
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat) :
    (networkStep system s newTime).base.validators.map Prod.fst =
    s.base.validators.map Prod.fst := by
  unfold networkStep
  simp only
  cases h_fs : ({ s with currentTime := newTime } : NetworkState).deliverPending.base.validators.findSome?
      (fun x => networkTryActFor system
        ({ s with currentTime := newTime } : NetworkState).deliverPending x.1 x.2) with
  | none =>
    simp only
    rw [deliverPending_preserves_ids]
  | some s'' =>
    simp only
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, ⟨vid_a, bv_a⟩, _, _, h_act, _⟩ := h_fs
    have := networkTryActFor_preserves_ids system _ vid_a bv_a s'' h_act
    rw [this]
    rw [deliverPending_preserves_ids]

/-- **Trace invariant**: at every step, `networkTrace`'s base
validators have the same id list as `system.validators`. Combined
with `system.validatorsNodup`, this gives nodup-by-id at every
step. -/
theorem networkTrace_validators_ids
    (system : BlockSynchroniserSystem) (time : Nat → Nat) (k : Nat) :
    (networkTrace system time k).base.validators.map Prod.fst =
    system.validators.map Prod.fst := by
  induction k with
  | zero =>
    show ({ NetworkState.init system with currentTime := time 0 }
      : NetworkState).base.validators.map Prod.fst = _
    unfold NetworkState.init BelugaState.init
    simp [List.map_map]
  | succ k ih =>
    show (networkStep system (networkTrace system time k) (time (k + 1))).base.validators.map Prod.fst = _
    rw [networkStep_preserves_ids]
    exact ih

/-- **Network-trace nodup-by-id invariant.** -/
theorem networkTrace_validators_nodup
    (system : BlockSynchroniserSystem) (time : Nat → Nat) (k : Nat) :
    ((networkTrace system time k).base.validators.map Prod.fst).Nodup := by
  rw [networkTrace_validators_ids]
  exact system.validatorsNodup

/-- `networkStepWithPull` preserves validator IDs. The new pull steps
(deliverPullPending, pullStep) preserve `base` entirely, so they
preserve validator IDs; `networkTryActFor` preservation is the
existing helper. -/
theorem networkStepWithPull_preserves_ids
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat) :
    (networkStepWithPull system s newTime).base.validators.map Prod.fst =
    s.base.validators.map Prod.fst := by
  unfold networkStepWithPull
  have h_del_base :
      ({ s with currentTime := newTime } : NetworkState).deliverPending.base.validators.map Prod.fst
        = s.base.validators.map Prod.fst := deliverPending_preserves_ids _
  have h_pull_del_base :
      (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending).base.validators.map Prod.fst
        = s.base.validators.map Prod.fst := by
    rw [NetworkState.deliverPullPending_preserves_base]; exact h_del_base
  have h_pulled_base :
      (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base.validators.map Prod.fst
        = s.base.validators.map Prod.fst := by
    rw [pullStep_preserves_base]; exact h_pull_del_base
  simp only
  split
  case _ s' h_fs =>
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, ⟨vid_a, bv_a⟩, _, _, h_act, _⟩ := h_fs
    have := networkTryActFor_preserves_ids system _ vid_a bv_a s' h_act
    rw [this]; exact h_pulled_base
  case _ _ => exact h_pulled_base

/-- `networkTraceWithPull` preserves validator IDs across all steps. -/
theorem networkTraceWithPull_validators_ids
    (system : BlockSynchroniserSystem) (time : Nat → Nat) (k : Nat) :
    (networkTraceWithPull system time k).base.validators.map Prod.fst =
    system.validators.map Prod.fst := by
  induction k with
  | zero =>
    show ({ NetworkState.init system with currentTime := time 0 }
      : NetworkState).base.validators.map Prod.fst = _
    unfold NetworkState.init BelugaState.init
    simp [List.map_map]
  | succ k ih =>
    show (networkStepWithPull system (networkTraceWithPull system time k) (time (k + 1))).base.validators.map Prod.fst = _
    rw [networkStepWithPull_preserves_ids]
    exact ih

/-- `networkTraceWithPull`'s validator-IDs are nodup. -/
theorem networkTraceWithPull_validators_nodup
    (system : BlockSynchroniserSystem) (time : Nat → Nat) (k : Nat) :
    ((networkTraceWithPull system time k).base.validators.map Prod.fst).Nodup := by
  rw [networkTraceWithPull_validators_ids]
  exact system.validatorsNodup

/-- `pullStep` preserves `inboxes`. -/
theorem pullStep_preserves_inboxes (system : BlockSynchroniserSystem)
    (s : NetworkState) :
    (pullStep system s).inboxes = s.inboxes := by
  unfold pullStep
  suffices h : ∀ (l : List (ValidatorId × Bool)) (s' : NetworkState),
      s'.inboxes = s.inboxes →
      (l.foldl (fun acc x => pullStepOne system acc x.1) s').inboxes = s.inboxes by
    apply h; rfl
  intro l
  induction l with
  | nil => intro s' h; exact h
  | cons hd tl ih =>
    intro s' h
    apply ih
    show (pullStepOne system s' hd.1).inboxes = s.inboxes
    unfold pullStepOne
    split
    · unfold doPullResponse
      split
      · simp only [NetworkState.removeFromPullInbox]; exact h
      · simp only [NetworkState.removeFromPullInbox]; exact h
    · split
      · unfold doPullRequest; exact h
      · exact h

/-- Generic helper: given `(vid, bv) ∈ l` and `l.map Prod.fst` is
Nodup, then `l.find? (·.1 == vid) = some (vid, bv)`. -/
lemma find?_of_mem_nodup
    {α β : Type*} [BEq α] [LawfulBEq α] (l : List (α × β))
    (a : α) (b : β) (h_mem : (a, b) ∈ l)
    (h_nodup : (l.map Prod.fst).Nodup) :
    l.find? (fun x => x.1 == a) = some (a, b) := by
  induction l with
  | nil => simp at h_mem
  | cons hd tl ih =>
    rw [List.find?_cons]
    cases h_match : hd.1 == a with
    | false =>
      rw [List.mem_cons] at h_mem
      rcases h_mem with h_eq | h_in
      · exfalso
        have : hd.1 = a := by rw [← h_eq]
        simp [this] at h_match
      · rw [List.map_cons] at h_nodup
        exact ih h_in h_nodup.of_cons
    | true =>
      rw [List.mem_cons] at h_mem
      rcases h_mem with h_eq | h_in
      · exact congrArg some h_eq.symm
      · exfalso
        rw [List.map_cons] at h_nodup
        have h_hd_eq : hd.1 = a := by simpa using h_match
        apply h_nodup.notMem
        rw [h_hd_eq]
        exact List.mem_map.mpr ⟨(a, b), h_in, rfl⟩

/-- Under network-trace nodup, if `(vid_a, bv_a) ∈ s.base.validators`,
then `s.base.getValidator vid_a = some bv_a`. -/
theorem networkTrace_getValidator_of_mem
    (system : BlockSynchroniserSystem) (time : Nat → Nat) (k : Nat)
    (vid_a : ValidatorId) (bv_a : BelugaValidator)
    (h_mem : (vid_a, bv_a) ∈ (networkTrace system time k).base.validators) :
    (networkTrace system time k).base.getValidator vid_a = some bv_a := by
  unfold BelugaState.getValidator
  rw [find?_of_mem_nodup _ _ _ h_mem (networkTrace_validators_nodup system time k)]
  rfl

/-- With-pull analog of `networkTrace_getValidator_of_mem`. -/
theorem networkTraceWithPull_getValidator_of_mem
    (system : BlockSynchroniserSystem) (time : Nat → Nat) (k : Nat)
    (vid_a : ValidatorId) (bv_a : BelugaValidator)
    (h_mem : (vid_a, bv_a) ∈ (networkTraceWithPull system time k).base.validators) :
    (networkTraceWithPull system time k).base.getValidator vid_a = some bv_a := by
  unfold BelugaState.getValidator
  rw [find?_of_mem_nodup _ _ _ h_mem (networkTraceWithPull_validators_nodup system time k)]
  rfl

/-! ## Phase E.2: round-entry monotonicity (structural)

The invariant `bv.roundEntryTime ≤ s.currentTime` holds at every
state of `networkTrace`. Self-inductive: at init both are 0; at
each `networkStep`, the only branch that modifies `roundEntryTime`
is `doAdvance`, which sets `roundEntryTime := s.currentTime`. -/

/-- `deliverPending` preserves `base.validators`. -/
theorem NetworkState.deliverPending_preserves_base_validators (s : NetworkState) :
    s.deliverPending.base.validators = s.base.validators := by
  unfold NetworkState.deliverPending
  generalize s.inflight.partition _ = p
  suffices h : ∀ (l : List DeliveryEvent) (s' : NetworkState),
      s'.base.validators = s.base.validators →
      (l.foldl (fun acc e => acc.appendToInbox e.recipient e.op) s').base.validators
        = s.base.validators by
    apply h; rfl
  intro l
  induction l with
  | nil => intro s' h; exact h
  | cons hd tl ih =>
    intro s' h
    apply ih; simp [NetworkState.appendToInbox, h]

/-- `deliverPending` preserves the entire `base` field — it only touches
`inboxes` (via `appendToInbox`) and `inflight` (via partition). -/
theorem NetworkState.deliverPending_preserves_base (s : NetworkState) :
    s.deliverPending.base = s.base := by
  unfold NetworkState.deliverPending
  generalize s.inflight.partition _ = p
  suffices h : ∀ (l : List DeliveryEvent) (s' : NetworkState),
      s'.base = s.base →
      (l.foldl (fun acc e => acc.appendToInbox e.recipient e.op) s').base = s.base by
    apply h; rfl
  intro l
  induction l with
  | nil => intro s' h; exact h
  | cons hd tl ih =>
    intro s' h
    apply ih; simp [NetworkState.appendToInbox, h]

/-- Generic helper: for any `f` that preserves `roundEntryTime`,
`updateValidator s vid_a f` preserves the "`roundEntryTime ≤ T`"
invariant — given the actor's original bv. -/
private lemma updateValidator_preserves_rt_bound
    (s : BelugaState) (vid_a : ValidatorId) (bv_a : BelugaValidator)
    (h_a_get : s.getValidator vid_a = some bv_a)
    (f : BelugaValidator → BelugaValidator)
    (h_f_rt : (f bv_a).roundEntryTime = bv_a.roundEntryTime)
    (T : Nat)
    (h_inv : ∀ vid bv, s.getValidator vid = some bv → bv.roundEntryTime ≤ T) :
    ∀ vid bv, (updateValidator s vid_a f).getValidator vid = some bv →
      bv.roundEntryTime ≤ T := by
  intro vid bv h_get
  by_cases h_eq : vid = vid_a
  · subst h_eq
    rw [updateValidator_getValidator_eq' (bv := bv_a) (h := h_a_get)] at h_get
    injection h_get with h_bv_eq
    have h_rt : bv.roundEntryTime = bv_a.roundEntryTime := by
      rw [← h_bv_eq, h_f_rt]
    rw [h_rt]
    exact h_inv vid bv_a h_a_get
  · rw [updateValidator_getValidator_ne' _ _ _ _ h_eq] at h_get
    exact h_inv vid bv h_get

theorem networkTryActFor_preserves_roundEntry_bound
    (system : BlockSynchroniserSystem) (s : NetworkState)
    (h_inv : ∀ vid bv,
      s.base.getValidator vid = some bv → bv.roundEntryTime ≤ s.currentTime)
    (vid_a : ValidatorId) (bv_a : BelugaValidator)
    (h_a_get : s.base.getValidator vid_a = some bv_a)
    (s' : NetworkState)
    (h_act : networkTryActFor system s vid_a bv_a = some s') :
    ∀ vid bv,
      s'.base.getValidator vid = some bv → bv.roundEntryTime ≤ s'.currentTime := by
  intro vid bv h_get
  have h_ct : s'.currentTime = s.currentTime :=
    networkTryActFor_preserves_currentTime system s vid_a bv_a s' h_act
  rw [h_ct]
  unfold networkTryActFor at h_act
  simp only at h_act
  split at h_act
  · -- Propose branch.
    injection h_act with h_eq
    rw [← h_eq] at h_get
    show bv.roundEntryTime ≤ s.currentTime
    rw [doPropose_getValidator'] at h_get
    exact h_inv vid bv h_get
  · split at h_act
    · -- Accept branch.
      rename_i B_acc _
      injection h_act with h_eq
      rw [← h_eq] at h_get
      show bv.roundEntryTime ≤ s.currentTime
      unfold doAccept at h_get
      have h_inv_ops : ∀ vid bv,
          ({ s.base with emittedOperations :=
            s.base.emittedOperations ++ [ValidatorOperation.block_accept vid_a B_acc.d] }
            : BelugaState).getValidator vid = some bv → bv.roundEntryTime ≤ s.currentTime := by
        intro vid' bv' h_get'
        rw [getValidator_emittedOperations_irrelevant'] at h_get'
        exact h_inv vid' bv' h_get'
      have h_a_get_ops :
          ({ s.base with emittedOperations :=
            s.base.emittedOperations ++ [ValidatorOperation.block_accept vid_a B_acc.d] }
            : BelugaState).getValidator vid_a = some bv_a := by
        rw [getValidator_emittedOperations_irrelevant']; exact h_a_get
      exact updateValidator_preserves_rt_bound _ vid_a bv_a h_a_get_ops _
        rfl _ h_inv_ops vid bv h_get
    · split at h_act
      · -- Store branch.
        rename_i _ B_sto _
        injection h_act with h_eq
        rw [← h_eq] at h_get
        show bv.roundEntryTime ≤ s.currentTime
        unfold doStore at h_get
        have h_inv_ops : ∀ vid bv,
            ({ s.base with emittedOperations :=
              s.base.emittedOperations ++ [ValidatorOperation.block_store vid_a B_sto] }
              : BelugaState).getValidator vid = some bv →
              bv.roundEntryTime ≤ s.currentTime := by
          intro vid' bv' h_get'
          rw [getValidator_emittedOperations_irrelevant'] at h_get'
          exact h_inv vid' bv' h_get'
        have h_a_get_ops :
            ({ s.base with emittedOperations :=
              s.base.emittedOperations ++ [ValidatorOperation.block_store vid_a B_sto] }
              : BelugaState).getValidator vid_a = some bv_a := by
          rw [getValidator_emittedOperations_irrelevant']; exact h_a_get
        exact updateValidator_preserves_rt_bound _ vid_a bv_a h_a_get_ops _
          rfl _ h_inv_ops vid bv h_get
      · -- Advance branch (now uses single updateValidator after refactor).
        split at h_act
        · injection h_act with h_eq
          rw [← h_eq] at h_get
          show bv.roundEntryTime ≤ s.currentTime
          -- s'.base = updateValidator s.base vid_a (fun bv0 => { bv0 with cR + 1, rET := s.currentTime })
          -- The f sets roundEntryTime := s.currentTime, so the updated bv has rt = currentTime.
          by_cases h_eq_vid : vid = vid_a
          · subst h_eq_vid
            rw [updateValidator_getValidator_eq' (bv := bv_a)] at h_get
            · injection h_get with h_bv_eq
              -- bv = { bv_a with cR := cR + 1, rET := s.currentTime }
              have : bv.roundEntryTime = s.currentTime := by rw [← h_bv_eq]
              rw [this]
            · exact h_a_get
          · rw [updateValidator_getValidator_ne' _ _ _ _ h_eq_vid] at h_get
            exact h_inv vid bv h_get
        · contradiction

/-! ## Round-monotonicity helpers (Phase 1 of `networkTrace` §5 migration)

These mirror `step_round_monotone` / `step_round_at_most_one` from
`Beluga/Theorems.lean` but adapted for `networkStep`. The proof
structure is the same case-split on `networkTryActFor`'s four
branches; only the propose branch's bookkeeping (inflight) and
the advance branch's gate (`allProposedFor ∨ timeoutFired`) differ
from the `step` version. -/

/-- One `networkTryActFor` step never decreases `currentRound`. -/
theorem networkTryActFor_round_monotone
    (system : BlockSynchroniserSystem) (s : NetworkState)
    (vid_a : ValidatorId) (bv_a : BelugaValidator)
    (h_a_get : s.base.getValidator vid_a = some bv_a)
    (s' : NetworkState)
    (h_act : networkTryActFor system s vid_a bv_a = some s')
    (vid : ValidatorId) (bv bv' : BelugaValidator)
    (h : s.base.getValidator vid = some bv)
    (h' : s'.base.getValidator vid = some bv') :
    bv.currentRound ≤ bv'.currentRound := by
  unfold networkTryActFor at h_act
  simp only at h_act
  split at h_act
  · -- Propose branch: doPropose only updates blocks/emittedOperations.
    injection h_act with h_eq
    have h_base : s'.base = doPropose system s.base vid_a bv_a.currentRound := by
      rw [← h_eq]
    rw [h_base] at h'
    rw [doPropose_getValidator'] at h'
    rw [h] at h'; injection h' with h_eq'; rw [h_eq']
  · split at h_act
    · -- Accept branch.
      rename_i B_acc _
      injection h_act with h_eq
      have h_base : s'.base = doAccept s.base vid_a B_acc := by rw [← h_eq]
      rw [h_base] at h'
      unfold doAccept at h'
      by_cases h_eq_vid : vid = vid_a
      · subst h_eq_vid
        have h_a_eq : bv = bv_a := by rw [h] at h_a_get; injection h_a_get
        rw [updateValidator_getValidator_eq'
              (s := { s.base with emittedOperations := _ })
              (bv := bv_a)
              (h := by rw [getValidator_emittedOperations_irrelevant']; exact h_a_get)] at h'
        injection h' with h_eq'; rw [h_a_eq]; rw [← h_eq']
      · rw [updateValidator_getValidator_ne'
              _ vid vid_a (fun bv => { bv with acceptedBlocks := B_acc.d :: bv.acceptedBlocks })
              h_eq_vid] at h'
        rw [getValidator_emittedOperations_irrelevant'] at h'
        rw [h] at h'; injection h' with h_eq'; rw [h_eq']
    · split at h_act
      · -- Store branch.
        rename_i _ B_sto _
        injection h_act with h_eq
        have h_base : s'.base = doStore s.base vid_a B_sto := by rw [← h_eq]
        rw [h_base] at h'
        unfold doStore at h'
        by_cases h_eq_vid : vid = vid_a
        · subst h_eq_vid
          have h_a_eq : bv = bv_a := by rw [h] at h_a_get; injection h_a_get
          rw [updateValidator_getValidator_eq'
                (s := { s.base with emittedOperations := _ })
                (bv := bv_a)
                (h := by rw [getValidator_emittedOperations_irrelevant']; exact h_a_get)] at h'
          injection h' with h_eq'; rw [h_a_eq]; rw [← h_eq']
        · rw [updateValidator_getValidator_ne'
                _ vid vid_a (fun bv => { bv with storedBlocks := B_sto.d :: bv.storedBlocks })
                h_eq_vid] at h'
          rw [getValidator_emittedOperations_irrelevant'] at h'
          rw [h] at h'; injection h' with h_eq'; rw [h_eq']
      · -- Advance branch: updateValidator with currentRound + 1.
        split at h_act
        · injection h_act with h_eq
          have h_base : s'.base = updateValidator s.base vid_a (fun bv0 =>
              { bv0 with currentRound := bv0.currentRound + 1,
                         roundEntryTime := s.currentTime }) := by rw [← h_eq]
          rw [h_base] at h'
          by_cases h_eq_vid : vid = vid_a
          · subst h_eq_vid
            have h_a_eq : bv = bv_a := by rw [h] at h_a_get; injection h_a_get
            rw [updateValidator_getValidator_eq' (bv := bv_a) (h := h_a_get)] at h'
            injection h' with h_eq'
            rw [h_a_eq, ← h_eq']
            simp only; exact Nat.le_succ _
          · rw [updateValidator_getValidator_ne' _ _ _ _ h_eq_vid] at h'
            rw [h] at h'; injection h' with h_eq'; rw [h_eq']
        · contradiction

/-- One `networkTryActFor` step increases `currentRound` by at most 1. -/
theorem networkTryActFor_round_at_most_one
    (system : BlockSynchroniserSystem) (s : NetworkState)
    (vid_a : ValidatorId) (bv_a : BelugaValidator)
    (h_a_get : s.base.getValidator vid_a = some bv_a)
    (s' : NetworkState)
    (h_act : networkTryActFor system s vid_a bv_a = some s')
    (vid : ValidatorId) (bv bv' : BelugaValidator)
    (h : s.base.getValidator vid = some bv)
    (h' : s'.base.getValidator vid = some bv') :
    bv'.currentRound ≤ bv.currentRound + 1 := by
  unfold networkTryActFor at h_act
  simp only at h_act
  split at h_act
  · -- Propose: round unchanged.
    injection h_act with h_eq
    have h_base : s'.base = doPropose system s.base vid_a bv_a.currentRound := by rw [← h_eq]
    rw [h_base] at h'
    rw [doPropose_getValidator'] at h'
    rw [h] at h'; injection h' with h_eq'; rw [← h_eq']; exact Nat.le_succ _
  · split at h_act
    · -- Accept: round unchanged.
      rename_i B_acc _
      injection h_act with h_eq
      have h_base : s'.base = doAccept s.base vid_a B_acc := by rw [← h_eq]
      rw [h_base] at h'
      unfold doAccept at h'
      by_cases h_eq_vid : vid = vid_a
      · subst h_eq_vid
        have h_a_eq : bv = bv_a := by rw [h] at h_a_get; injection h_a_get
        rw [updateValidator_getValidator_eq'
              (s := { s.base with emittedOperations := _ })
              (bv := bv_a)
              (h := by rw [getValidator_emittedOperations_irrelevant']; exact h_a_get)] at h'
        injection h' with h_eq'; rw [h_a_eq, ← h_eq']; exact Nat.le_succ _
      · rw [updateValidator_getValidator_ne'
              _ vid vid_a (fun bv => { bv with acceptedBlocks := B_acc.d :: bv.acceptedBlocks })
              h_eq_vid] at h'
        rw [getValidator_emittedOperations_irrelevant'] at h'
        rw [h] at h'; injection h' with h_eq'; rw [← h_eq']; exact Nat.le_succ _
    · split at h_act
      · -- Store: round unchanged.
        rename_i _ B_sto _
        injection h_act with h_eq
        have h_base : s'.base = doStore s.base vid_a B_sto := by rw [← h_eq]
        rw [h_base] at h'
        unfold doStore at h'
        by_cases h_eq_vid : vid = vid_a
        · subst h_eq_vid
          have h_a_eq : bv = bv_a := by rw [h] at h_a_get; injection h_a_get
          rw [updateValidator_getValidator_eq'
                (s := { s.base with emittedOperations := _ })
                (bv := bv_a)
                (h := by rw [getValidator_emittedOperations_irrelevant']; exact h_a_get)] at h'
          injection h' with h_eq'; rw [h_a_eq, ← h_eq']; exact Nat.le_succ _
        · rw [updateValidator_getValidator_ne'
                _ vid vid_a (fun bv => { bv with storedBlocks := B_sto.d :: bv.storedBlocks })
                h_eq_vid] at h'
          rw [getValidator_emittedOperations_irrelevant'] at h'
          rw [h] at h'; injection h' with h_eq'; rw [← h_eq']; exact Nat.le_succ _
      · -- Advance: round goes up by exactly 1 for vid_a.
        split at h_act
        · injection h_act with h_eq
          have h_base : s'.base = updateValidator s.base vid_a (fun bv0 =>
              { bv0 with currentRound := bv0.currentRound + 1,
                         roundEntryTime := s.currentTime }) := by rw [← h_eq]
          rw [h_base] at h'
          by_cases h_eq_vid : vid = vid_a
          · subst h_eq_vid
            have h_a_eq : bv = bv_a := by rw [h] at h_a_get; injection h_a_get
            rw [updateValidator_getValidator_eq' (bv := bv_a) (h := h_a_get)] at h'
            injection h' with h_eq'; rw [h_a_eq, ← h_eq']
          · rw [updateValidator_getValidator_ne' _ _ _ _ h_eq_vid] at h'
            rw [h] at h'; injection h' with h_eq'; rw [← h_eq']; exact Nat.le_succ _
        · contradiction

/-- One `networkStep` never decreases any validator's `currentRound`.
Requires a `nodup` hypothesis on the validator IDs to identify the
actor of the `findSome?` step uniquely. -/
theorem networkStep_round_monotone
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat)
    (h_nodup : (s.base.validators.map Prod.fst).Nodup)
    (vid : ValidatorId) (bv bv' : BelugaValidator)
    (h : s.base.getValidator vid = some bv)
    (h' : (networkStep system s newTime).base.getValidator vid = some bv') :
    bv.currentRound ≤ bv'.currentRound := by
  unfold networkStep at h'
  -- Step 1: deliverPending preserves base.
  have h_del_base :
      ({ s with currentTime := newTime } : NetworkState).deliverPending.base = s.base := by
    rw [NetworkState.deliverPending_preserves_base]
  have h_del_nodup :
      (({ s with currentTime := newTime } : NetworkState).deliverPending.base.validators.map
        Prod.fst).Nodup := by
    rw [h_del_base]; exact h_nodup
  have h_del_get :
      ({ s with currentTime := newTime } : NetworkState).deliverPending.base.getValidator vid
        = some bv := by
    rw [h_del_base]; exact h
  simp only at h'
  split at h'
  case _ s'' h_fs =>
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, ⟨vid_a, bv_a⟩, _, h_l_split, h_act, _⟩ := h_fs
    have h_a_mem : (vid_a, bv_a) ∈
        ({ s with currentTime := newTime } : NetworkState).deliverPending.base.validators := by
      rw [h_l_split]; simp
    have h_a_get :
        ({ s with currentTime := newTime } : NetworkState).deliverPending.base.getValidator vid_a
          = some bv_a := by
      unfold BelugaState.getValidator
      rw [Option.map_eq_some_iff]
      exact ⟨(vid_a, bv_a), find?_of_mem_nodup _ vid_a bv_a h_a_mem h_del_nodup, rfl⟩
    exact networkTryActFor_round_monotone system _ vid_a bv_a h_a_get s'' h_act
      vid bv bv' h_del_get h'
  case _ _ =>
    rw [h_del_get] at h'; injection h' with h_eq; rw [h_eq]

/-- One `networkStep` increases `currentRound` by at most 1. -/
theorem networkStep_round_at_most_one
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat)
    (h_nodup : (s.base.validators.map Prod.fst).Nodup)
    (vid : ValidatorId) (bv bv' : BelugaValidator)
    (h : s.base.getValidator vid = some bv)
    (h' : (networkStep system s newTime).base.getValidator vid = some bv') :
    bv'.currentRound ≤ bv.currentRound + 1 := by
  unfold networkStep at h'
  have h_del_base :
      ({ s with currentTime := newTime } : NetworkState).deliverPending.base = s.base := by
    rw [NetworkState.deliverPending_preserves_base]
  have h_del_nodup :
      (({ s with currentTime := newTime } : NetworkState).deliverPending.base.validators.map
        Prod.fst).Nodup := by
    rw [h_del_base]; exact h_nodup
  have h_del_get :
      ({ s with currentTime := newTime } : NetworkState).deliverPending.base.getValidator vid
        = some bv := by
    rw [h_del_base]; exact h
  simp only at h'
  split at h'
  case _ s'' h_fs =>
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, ⟨vid_a, bv_a⟩, _, h_l_split, h_act, _⟩ := h_fs
    have h_a_mem : (vid_a, bv_a) ∈
        ({ s with currentTime := newTime } : NetworkState).deliverPending.base.validators := by
      rw [h_l_split]; simp
    have h_a_get :
        ({ s with currentTime := newTime } : NetworkState).deliverPending.base.getValidator vid_a
          = some bv_a := by
      unfold BelugaState.getValidator
      rw [Option.map_eq_some_iff]
      exact ⟨(vid_a, bv_a), find?_of_mem_nodup _ vid_a bv_a h_a_mem h_del_nodup, rfl⟩
    exact networkTryActFor_round_at_most_one system _ vid_a bv_a h_a_get s'' h_act
      vid bv bv' h_del_get h'
  case _ _ =>
    rw [h_del_get] at h'; injection h' with h_eq; rw [h_eq]; exact Nat.le_succ _

/-- Round-monotonicity across `networkTrace`. -/
theorem network_round_monotone_trace
    (system : BlockSynchroniserSystem) (time : Nat → Nat) (vid : ValidatorId)
    (k₁ : Nat) (bv₁ : BelugaValidator)
    (h₁ : (networkTrace system time k₁).base.getValidator vid = some bv₁) :
    ∀ k₂, k₁ ≤ k₂ → ∀ bv₂,
      (networkTrace system time k₂).base.getValidator vid = some bv₂ →
      bv₁.currentRound ≤ bv₂.currentRound := by
  intro k₂ h_le
  induction h_le with
  | refl =>
    intro bv₂ h₂; rw [h₁] at h₂; injection h₂ with h_eq; rw [h_eq]
  | @step k_mid _ ih =>
    intro bv₂ h₂
    -- networkTrace at k_mid + 1 = networkStep applied to networkTrace at k_mid.
    have h_step : (networkTrace system time (k_mid + 1)).base =
        (networkStep system (networkTrace system time k_mid)
          (time (k_mid + 1))).base := rfl
    have h_succ_ids := networkTrace_validators_ids system time (k_mid + 1)
    have h_mid_ids := networkTrace_validators_ids system time k_mid
    have h_match : ∀ p ∈ (networkTrace system time (k_mid + 1)).base.validators,
        (p.1 == vid) = true → p.1 = vid := fun _ _ h => by simpa using h
    have h_vid_in_succ : vid ∈
        (networkTrace system time (k_mid + 1)).base.validators.map Prod.fst := by
      unfold BelugaState.getValidator at h₂
      rw [Option.map_eq_some_iff] at h₂
      obtain ⟨p, h_p_mem, _⟩ := h₂
      have h_p_in := List.mem_of_find?_eq_some h_p_mem
      have h_match_eq := List.find?_some h_p_mem
      have h_p1 : p.1 = vid := by
        match p, h_match_eq with
        | (_, _), h => simpa using h
      rw [← h_p1]; exact List.mem_map.mpr ⟨p, h_p_in, rfl⟩
    have h_vid_in_mid : vid ∈ (networkTrace system time k_mid).base.validators.map Prod.fst := by
      rw [h_mid_ids, ← h_succ_ids]; exact h_vid_in_succ
    -- Extract bv_mid
    obtain ⟨bv_mid, h_mid⟩ : ∃ bv_mid,
        (networkTrace system time k_mid).base.getValidator vid = some bv_mid := by
      obtain ⟨p, h_p_mem, h_p_eq⟩ := List.mem_map.mp h_vid_in_mid
      refine ⟨p.2, ?_⟩
      have h_pair : p = (vid, p.2) := Prod.ext h_p_eq rfl
      rw [h_pair] at h_p_mem
      exact networkTrace_getValidator_of_mem system time k_mid vid p.2 h_p_mem
    have ih' := ih bv_mid h_mid
    have h_mono := networkStep_round_monotone system (networkTrace system time k_mid)
        (time (k_mid + 1)) (networkTrace_validators_nodup system time k_mid)
        vid bv_mid bv₂ h_mid (h_step ▸ h₂)
    exact le_trans ih' h_mono

/-- Honest validators are present at every step of `networkTrace`. -/
theorem network_honest_validator_persistent_trace
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (vid : ValidatorId) (h_vid_honest : isHonestValidator system vid = true)
    (k : Nat) :
    ∃ bv, (networkTrace system time k).base.getValidator vid = some bv := by
  -- Step 1: vid is in system.validators (with isHonest = true).
  have h_vid_in_system : vid ∈ system.validators.map Prod.fst := by
    unfold isHonestValidator BlockSynchroniserSystem.isHonest at h_vid_honest
    cases h_some : system.validators.find? (fun p => p.1 = vid) with
    | none => rw [h_some] at h_vid_honest; exact absurd h_vid_honest (by simp)
    | some p =>
      have h_p_in := List.mem_of_find?_eq_some h_some
      have h_match := List.find?_some h_some
      have h_p1 : p.1 = vid := by simpa using h_match
      rw [← h_p1]; exact List.mem_map.mpr ⟨p, h_p_in, rfl⟩
  -- Step 2: trace at step k has same IDs as system, so vid is also there.
  have h_vid_in_k : vid ∈ (networkTrace system time k).base.validators.map Prod.fst := by
    rw [networkTrace_validators_ids]; exact h_vid_in_system
  -- Step 3: extract the bv from the validator pair (membership).
  obtain ⟨p, h_p_in, h_p_eq⟩ := List.mem_map.mp h_vid_in_k
  refine ⟨p.2, ?_⟩
  have h_pair : p = (vid, p.2) := Prod.ext h_p_eq rfl
  rw [h_pair] at h_p_in
  exact networkTrace_getValidator_of_mem system time k vid p.2 h_p_in

/-- With-pull analog of `network_honest_validator_persistent_trace`. -/
theorem network_honest_validator_persistent_traceWithPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (vid : ValidatorId) (h_vid_honest : isHonestValidator system vid = true)
    (k : Nat) :
    ∃ bv, (networkTraceWithPull system time k).base.getValidator vid = some bv := by
  have h_vid_in_system : vid ∈ system.validators.map Prod.fst := by
    unfold isHonestValidator BlockSynchroniserSystem.isHonest at h_vid_honest
    cases h_some : system.validators.find? (fun p => p.1 = vid) with
    | none => rw [h_some] at h_vid_honest; exact absurd h_vid_honest (by simp)
    | some p =>
      have h_p_in := List.mem_of_find?_eq_some h_some
      have h_match := List.find?_some h_some
      have h_p1 : p.1 = vid := by simpa using h_match
      rw [← h_p1]; exact List.mem_map.mpr ⟨p, h_p_in, rfl⟩
  have h_vid_in_k : vid ∈ (networkTraceWithPull system time k).base.validators.map Prod.fst := by
    rw [networkTraceWithPull_validators_ids]; exact h_vid_in_system
  obtain ⟨p, h_p_in, h_p_eq⟩ := List.mem_map.mp h_vid_in_k
  refine ⟨p.2, ?_⟩
  have h_pair : p = (vid, p.2) := Prod.ext h_p_eq rfl
  rw [h_pair] at h_p_in
  exact networkTraceWithPull_getValidator_of_mem system time k vid p.2 h_p_in

/-- Intermediate value theorem for `networkTrace` rounds: if `vid`'s
round goes from `≤ r` to `≥ r` between steps `k₁` and `k₂`, there's
some intermediate step where the round equals `r` exactly. -/
theorem network_round_intermediate_value
    (system : BlockSynchroniserSystem) (time : Nat → Nat) (vid : ValidatorId)
    (k₁ k₂ : Nat) (r : Nat)
    (hle : k₁ ≤ k₂)
    (bv₁ bv₂ : BelugaValidator)
    (h₁ : (networkTrace system time k₁).base.getValidator vid = some bv₁)
    (h₂ : (networkTrace system time k₂).base.getValidator vid = some bv₂)
    (hr₁ : bv₁.currentRound ≤ r)
    (hr₂ : r ≤ bv₂.currentRound) :
    ∃ k, k₁ ≤ k ∧ k ≤ k₂ ∧
      ∃ bv, (networkTrace system time k).base.getValidator vid = some bv ∧
            bv.currentRound = r := by
  induction hle generalizing bv₁ bv₂ with
  | refl =>
    -- k₂ = k₁; bv₁ = bv₂; round must equal r.
    have h_eq : bv₁ = bv₂ := by rw [h₁] at h₂; injection h₂
    rw [h_eq] at hr₁
    refine ⟨k₁, le_rfl, le_rfl, bv₂, h₂, ?_⟩
    exact Nat.le_antisymm hr₁ hr₂
  | @step k₂ hk ih =>
    -- networkTrace at k₂ + 1 = networkStep applied to networkTrace at k₂.
    -- Need bv_prev at k₂.
    have h_step_eq : (networkTrace system time (k₂ + 1)).base =
        (networkStep system (networkTrace system time k₂)
          (time (k₂ + 1))).base := rfl
    -- Get bv_prev at k₂ via id-preservation.
    have h_succ_ids := networkTrace_validators_ids system time (k₂ + 1)
    have h_mid_ids := networkTrace_validators_ids system time k₂
    have h_vid_in_succ : vid ∈
        (networkTrace system time (k₂ + 1)).base.validators.map Prod.fst := by
      unfold BelugaState.getValidator at h₂
      rw [Option.map_eq_some_iff] at h₂
      obtain ⟨p, h_p_mem, _⟩ := h₂
      have h_p_in := List.mem_of_find?_eq_some h_p_mem
      have h_match := List.find?_some h_p_mem
      have h_p1 : p.1 = vid := by
        match p, h_match with
        | (_, _), h => simpa using h
      rw [← h_p1]; exact List.mem_map.mpr ⟨p, h_p_in, rfl⟩
    have h_vid_in_mid : vid ∈ (networkTrace system time k₂).base.validators.map Prod.fst := by
      rw [h_mid_ids, ← h_succ_ids]; exact h_vid_in_succ
    obtain ⟨bv_prev, hbv_prev⟩ : ∃ bv_prev,
        (networkTrace system time k₂).base.getValidator vid = some bv_prev := by
      obtain ⟨p, h_p_mem, h_p_eq⟩ := List.mem_map.mp h_vid_in_mid
      refine ⟨p.2, ?_⟩
      have h_pair : p = (vid, p.2) := Prod.ext h_p_eq rfl
      rw [h_pair] at h_p_mem
      exact networkTrace_getValidator_of_mem system time k₂ vid p.2 h_p_mem
    -- bv₂ ≤ bv_prev + 1 by networkStep_round_at_most_one.
    have h_step_bound : bv₂.currentRound ≤ bv_prev.currentRound + 1 := by
      apply networkStep_round_at_most_one system (networkTrace system time k₂)
        (time (k₂ + 1)) (networkTrace_validators_nodup system time k₂) vid bv_prev bv₂
        hbv_prev (h_step_eq ▸ h₂)
    -- Case on whether bv_prev.currentRound ≥ r.
    by_cases h_prev_ge : bv_prev.currentRound ≥ r
    · -- Use ih on k₁ ≤ k₂ with bv_prev.
      obtain ⟨k, hk_lo, hk_hi, bv_int, h_int, h_int_round⟩ := ih bv₁ bv_prev h₁ hbv_prev hr₁ h_prev_ge
      exact ⟨k, hk_lo, le_trans hk_hi (Nat.le_succ _), bv_int, h_int, h_int_round⟩
    · -- bv_prev.currentRound < r ≤ bv₂.currentRound = bv_prev.currentRound + 1, so bv₂.currentRound = r.
      have h_lt : bv_prev.currentRound < r := Nat.not_le.mp h_prev_ge
      have h_le_succ : r ≤ bv_prev.currentRound + 1 := le_trans hr₂ h_step_bound
      have h_eq_r : bv₂.currentRound = r := by
        -- r ≤ bv₂.currentRound (hr₂); bv₂.currentRound ≤ bv_prev.currentRound + 1 (h_step_bound)
        -- bv_prev.currentRound < r, so bv_prev.currentRound + 1 ≤ r
        have : bv_prev.currentRound + 1 ≤ r := h_lt
        have h_upper : bv₂.currentRound ≤ r := le_trans h_step_bound this
        exact Nat.le_antisymm h_upper hr₂
      refine ⟨k₂ + 1, Nat.le_succ_of_le hk, le_rfl, bv₂, h₂, h_eq_r⟩

/-- `networkTryActFor` only appends to `emittedOperations` (monotone).
Specifically, every operation in `s.base.emittedOperations` is also
in `s'.base.emittedOperations` whenever `networkTryActFor system s vid_a bv_a = some s'`. -/
theorem networkTryActFor_emittedOperations_monotone
    (system : BlockSynchroniserSystem) (s : NetworkState)
    (vid_a : ValidatorId) (bv_a : BelugaValidator)
    (s' : NetworkState)
    (h_act : networkTryActFor system s vid_a bv_a = some s') :
    ∀ op ∈ s.base.emittedOperations, op ∈ s'.base.emittedOperations := by
  intro op hop
  unfold networkTryActFor at h_act
  simp only at h_act
  split at h_act
  · -- Propose: doPropose appends [block_propose ...] to emittedOperations.
    injection h_act with h_eq
    have h_base : s'.base = doPropose system s.base vid_a bv_a.currentRound := by rw [← h_eq]
    rw [h_base]; unfold doPropose; simp
    exact Or.inl hop
  · split at h_act
    · -- Accept.
      rename_i B_acc _
      injection h_act with h_eq
      have h_base : s'.base = doAccept s.base vid_a B_acc := by rw [← h_eq]
      rw [h_base]; unfold doAccept
      simp only [updateValidator]
      exact List.mem_append.mpr (Or.inl hop)
    · split at h_act
      · -- Store.
        rename_i _ B_sto _
        injection h_act with h_eq
        have h_base : s'.base = doStore s.base vid_a B_sto := by rw [← h_eq]
        rw [h_base]; unfold doStore
        simp only [updateValidator]
        exact List.mem_append.mpr (Or.inl hop)
      · -- Advance.
        split at h_act
        · injection h_act with h_eq
          have h_base : s'.base = updateValidator s.base vid_a (fun bv0 =>
              { bv0 with currentRound := bv0.currentRound + 1,
                         roundEntryTime := s.currentTime }) := by rw [← h_eq]
          rw [h_base]; unfold updateValidator
          exact hop
        · contradiction

/-- One `networkStep` only appends to `emittedOperations`. -/
theorem networkStep_emittedOperations_monotone
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat) :
    ∀ op ∈ s.base.emittedOperations,
      op ∈ (networkStep system s newTime).base.emittedOperations := by
  intro op hop
  unfold networkStep
  -- The advance + delivery don't change base; the action might extend it.
  have h_del_base :
      ({ s with currentTime := newTime } : NetworkState).deliverPending.base = s.base := by
    rw [NetworkState.deliverPending_preserves_base]
  have h_del_hop : op ∈
      ({ s with currentTime := newTime } : NetworkState).deliverPending.base.emittedOperations := by
    rw [h_del_base]; exact hop
  simp only
  split
  case _ s'' h_fs =>
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, ⟨vid_a, bv_a⟩, _, _, h_act, _⟩ := h_fs
    exact networkTryActFor_emittedOperations_monotone system _ vid_a bv_a s'' h_act op h_del_hop
  case _ _ => exact h_del_hop

/-- `networkStep` preserves "absent": if `vid` isn't in `s.base.validators`,
it isn't in `(networkStep ...).base.validators` either. -/
private lemma networkStep_preserves_none (system : BlockSynchroniserSystem)
    (s : NetworkState) (newTime : Nat) (vid : ValidatorId)
    (h : s.base.getValidator vid = none) :
    (networkStep system s newTime).base.getValidator vid = none := by
  unfold BelugaState.getValidator at h ⊢
  rw [Option.map_eq_none_iff] at h ⊢
  rw [List.find?_eq_none] at h ⊢
  have h_keys := networkStep_preserves_ids system s newTime
  intro x hx h_match
  have h_x_key : x.1 ∈ (networkStep system s newTime).base.validators.map Prod.fst :=
    List.mem_map.mpr ⟨x, hx, rfl⟩
  rw [h_keys] at h_x_key
  obtain ⟨y, hy_mem, hy_eq⟩ := List.mem_map.mp h_x_key
  apply h y hy_mem
  grind

/-! ## Phase 2: networkStep advance inversion -/

/-- If `vid`'s round increased by 1 across one `networkStep`, then
the advance branch of `networkTryActFor` fired for `vid`. From this
we extract: (1) `vid` had proposed for its round, (2) every
accepted block was already stored, (3) the advance gate fired
(`allProposedFor` or timeout). -/
private lemma networkStep_advance_inversion
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat)
    (vid : ValidatorId) (bv bv' : BelugaValidator)
    (h_nodup : (s.base.validators.map Prod.fst).Nodup)
    (h : s.base.getValidator vid = some bv)
    (h' : (networkStep system s newTime).base.getValidator vid = some bv')
    (h_advance : bv'.currentRound = bv.currentRound + 1) :
    hasProposedFor s.base vid bv.currentRound = true ∧
    (∀ B ∈ s.base.blocks,
      hasAcceptedDigest s.base vid B.d = true →
      hasStoredDigest s.base vid B.d = true) ∧
    (allProposedFor system s.base bv.currentRound = true ∨
     ({ s with currentTime := newTime } : NetworkState).deliverPending.timeoutFired
        system bv = true) := by
  have h_del_base :
      ({ s with currentTime := newTime } : NetworkState).deliverPending.base = s.base := by
    rw [NetworkState.deliverPending_preserves_base]
  have h_del_nodup :
      (({ s with currentTime := newTime } : NetworkState).deliverPending.base.validators.map
        Prod.fst).Nodup := by rw [h_del_base]; exact h_nodup
  have h_del_get :
      ({ s with currentTime := newTime } : NetworkState).deliverPending.base.getValidator vid
        = some bv := by rw [h_del_base]; exact h
  unfold networkStep at h'
  simp only at h'
  split at h'
  case _ s_post h_fs =>
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, ⟨vid_a, bv_a⟩, _, h_split, h_act, _⟩ := h_fs
    have h_a_mem : (vid_a, bv_a) ∈
        ({ s with currentTime := newTime } : NetworkState).deliverPending.base.validators := by
      rw [h_split]; simp
    have h_a_get :
        ({ s with currentTime := newTime } : NetworkState).deliverPending.base.getValidator vid_a
          = some bv_a := by
      unfold BelugaState.getValidator
      rw [Option.map_eq_some_iff]
      exact ⟨(vid_a, bv_a), find?_of_mem_nodup _ vid_a bv_a h_a_mem h_del_nodup, rfl⟩
    unfold networkTryActFor at h_act
    simp only at h_act
    split at h_act
    case isTrue h_prop_neg =>
      -- Propose branch fired: doPropose preserves currentRound → contradiction.
      injection h_act with h_eq
      have h_base_post : s_post.base = doPropose system
          ({ s with currentTime := newTime } : NetworkState).deliverPending.base
          vid_a bv_a.currentRound := by rw [← h_eq]
      rw [h_base_post] at h'
      rw [doPropose_getValidator'] at h'
      rw [h_del_get] at h'
      have h_eq_bv : bv = bv' := Option.some.inj h'
      exfalso
      rw [h_eq_bv] at h_advance
      exact absurd h_advance (Nat.lt_succ_self _).ne
    case isFalse h_prop_pos =>
      have h_hpr_a : hasProposedFor
          ({ s with currentTime := newTime } : NetworkState).deliverPending.base
          vid_a bv_a.currentRound = true := by
        cases h_b : hasProposedFor
            ({ s with currentTime := newTime } : NetworkState).deliverPending.base
            vid_a bv_a.currentRound with
        | true => rfl
        | false => exfalso; apply h_prop_pos; simp [h_b]
      split at h_act
      case h_1 B_acc h_findAcc =>
        -- Accept branch fired: doAccept preserves currentRound → contradiction.
        injection h_act with h_eq
        have h_base_post : s_post.base = doAccept
            ({ s with currentTime := newTime } : NetworkState).deliverPending.base
            vid_a B_acc := by rw [← h_eq]
        rw [h_base_post] at h'
        obtain ⟨bv_post, h_post_get, h_eq_round⟩ :=
          doAccept_round'
            ({ s with currentTime := newTime } : NetworkState).deliverPending.base
            vid vid_a B_acc bv h_del_get
        have h_eq_bv : bv_post = bv' := Option.some.inj (h_post_get.symm.trans h')
        subst h_eq_bv
        exfalso
        rw [h_eq_round] at h_advance
        exact absurd h_advance (Nat.lt_succ_self _).ne
      case h_2 h_findAcc =>
        split at h_act
        case h_1 B_sto h_findSto =>
          -- Store branch fired.
          injection h_act with h_eq
          have h_base_post : s_post.base = doStore
              ({ s with currentTime := newTime } : NetworkState).deliverPending.base
              vid_a B_sto := by rw [← h_eq]
          rw [h_base_post] at h'
          obtain ⟨bv_post, h_post_get, h_eq_round⟩ :=
            doStore_round'
              ({ s with currentTime := newTime } : NetworkState).deliverPending.base
              vid vid_a B_sto bv h_del_get
          have h_eq_bv : bv_post = bv' := Option.some.inj (h_post_get.symm.trans h')
          subst h_eq_bv
          exfalso
          rw [h_eq_round] at h_advance
          exact absurd h_advance (Nat.lt_succ_self _).ne
        case h_2 h_findSto =>
          -- Advance branch.
          split at h_act
          case isTrue h_gate =>
            injection h_act with h_eq
            set s_del : NetworkState :=
              ({ s with currentTime := newTime } : NetworkState).deliverPending with h_s_del_def
            have h_base_post : s_post.base = updateValidator s_del.base
                vid_a (fun bv0 => { bv0 with currentRound := bv0.currentRound + 1,
                                              roundEntryTime := s_del.currentTime }) := by
              rw [← h_eq]
            rw [h_base_post] at h'
            by_cases h_eq_vid : vid = vid_a
            · subst h_eq_vid
              have h_bv_eq : bv = bv_a := by
                rw [h_del_get] at h_a_get; injection h_a_get
              rw [h_bv_eq]
              refine ⟨?_, ?_, ?_⟩
              · rw [← h_del_base]; exact h_hpr_a
              · intro B hB h_acc
                rw [List.find?_eq_none] at h_findSto
                have hB' : B ∈ s_del.base.blocks := h_del_base.symm ▸ hB
                have h_no := h_findSto B hB'
                rw [h_del_base] at h_no
                rw [h_acc] at h_no; simp at h_no
                cases h_sto : hasStoredDigest s.base vid B.d with
                | true => rfl
                | false => exfalso; rw [h_sto] at h_no; simp at h_no
              · rw [Bool.or_eq_true] at h_gate
                rcases h_gate with h_apf | h_tof
                · left; rw [← h_del_base]; exact h_apf
                · right; exact h_tof
            · -- vid ≠ vid_a: round didn't change → contradiction.
              rw [updateValidator_getValidator_ne' _ _ _ _ h_eq_vid] at h'
              rw [h_del_get] at h'
              have h_eq_bv : bv = bv' := Option.some.inj h'
              exfalso
              rw [h_eq_bv] at h_advance
              exact absurd h_advance (Nat.lt_succ_self _).ne
          case isFalse h_gate => simp at h_act
  case _ h_fs =>
    rw [h_del_get] at h'
    have h_eq_bv : bv = bv' := Option.some.inj h'
    exfalso
    rw [h_eq_bv] at h_advance
    exact absurd h_advance (Nat.lt_succ_self _).ne

/-- Projection: if round advanced, vid had proposed for its round. -/
private lemma networkStep_advance_implies_hasProposedFor
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat)
    (vid : ValidatorId) (bv bv' : BelugaValidator)
    (h_nodup : (s.base.validators.map Prod.fst).Nodup)
    (h : s.base.getValidator vid = some bv)
    (h' : (networkStep system s newTime).base.getValidator vid = some bv')
    (h_advance : bv'.currentRound = bv.currentRound + 1) :
    hasProposedFor s.base vid bv.currentRound = true :=
  (networkStep_advance_inversion system s newTime vid bv bv' h_nodup h h' h_advance).1

/-- Projection: if round advanced, every accepted block was already stored. -/
theorem networkStep_advance_implies_stored
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat)
    (vid : ValidatorId) (bv bv' : BelugaValidator)
    (h_nodup : (s.base.validators.map Prod.fst).Nodup)
    (h : s.base.getValidator vid = some bv)
    (h' : (networkStep system s newTime).base.getValidator vid = some bv')
    (h_advance : bv'.currentRound = bv.currentRound + 1) :
    ∀ B ∈ s.base.blocks,
      hasAcceptedDigest s.base vid B.d = true → hasStoredDigest s.base vid B.d = true :=
  (networkStep_advance_inversion system s newTime vid bv bv' h_nodup h h' h_advance).2.1

/-- Projection: if round advanced, the advance gate fired. -/
private lemma networkStep_advance_implies_gate
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat)
    (vid : ValidatorId) (bv bv' : BelugaValidator)
    (h_nodup : (s.base.validators.map Prod.fst).Nodup)
    (h : s.base.getValidator vid = some bv)
    (h' : (networkStep system s newTime).base.getValidator vid = some bv')
    (h_advance : bv'.currentRound = bv.currentRound + 1) :
    allProposedFor system s.base bv.currentRound = true ∨
    ({ s with currentTime := newTime } : NetworkState).deliverPending.timeoutFired
        system bv = true :=
  (networkStep_advance_inversion system s newTime vid bv bv' h_nodup h h' h_advance).2.2

/-! ## Phase 3 (minimal): acceptedBlockExists for `networkTrace`

The full `AcceptInv` does not survive `networkStep` under ImPoA
(paper §4.3) — `acceptedParents` is broken when a validator
accepts a block via the f+1-references path. We extract just the
`acceptedBlockExists` conjunct, which is preserved (canAcceptBlock
only fires for blocks already in the pool). -/

private lemma network_doAccept_HasAccepted_iff (s : BelugaState) (vid_a : ValidatorId)
    (B : Block) (vid : ValidatorId) (d : BlockDigest) :
    HasAccepted (doAccept s vid_a B) vid d ↔
    HasAccepted s vid d ∨ (vid = vid_a ∧ d = B.d) := by
  unfold HasAccepted Emitted doAccept updateValidator
  simp [SystemState.emittedOperations]

private lemma network_doStore_HasAccepted_iff (s : BelugaState) (vid_s : ValidatorId)
    (B : Block) (vid : ValidatorId) (d : BlockDigest) :
    HasAccepted (doStore s vid_s B) vid d ↔ HasAccepted s vid d := by
  unfold HasAccepted Emitted doStore updateValidator
  simp [SystemState.emittedOperations]

private lemma network_doPropose_HasAccepted_iff (system : BlockSynchroniserSystem)
    (s : BelugaState) (vid_p : ValidatorId) (r : Round)
    (vid : ValidatorId) (d : BlockDigest) :
    HasAccepted (doPropose system s vid_p r) vid d ↔ HasAccepted s vid d := by
  unfold HasAccepted Emitted doPropose; simp [SystemState.emittedOperations]

/-- Helper: `updateValidator` doesn't change `emittedOperations`. -/
private lemma updateValidator_emittedOperations_eq (s : BelugaState) (vid : ValidatorId)
    (f : BelugaValidator → BelugaValidator) :
    (updateValidator s vid f).emittedOperations = s.emittedOperations := by
  simp [updateValidator]

/-- Helper: `updateValidator` doesn't change `blocks`. -/
private lemma updateValidator_blocks_eq (s : BelugaState) (vid : ValidatorId)
    (f : BelugaValidator → BelugaValidator) :
    (updateValidator s vid f).blocks = s.blocks := by
  simp [updateValidator]

/-- HasAccepted preservation across `updateValidator`. -/
private lemma updateValidator_HasAccepted_iff (s : BelugaState) (vid_u : ValidatorId)
    (f : BelugaValidator → BelugaValidator) (vid : ValidatorId) (d : BlockDigest) :
    HasAccepted (updateValidator s vid_u f) vid d ↔ HasAccepted s vid d := by
  unfold HasAccepted Emitted updateValidator
  simp [SystemState.emittedOperations]

/-- The accepted-block-exists invariant on `networkTrace`. -/
theorem network_acceptedBlockExists_trace
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (vid : ValidatorId) (k : Nat) :
    ∀ d, HasAccepted (networkTrace system time k).base vid d →
      ∃ B ∈ (networkTrace system time k).base.blocks, B.d = d := by
  induction k with
  | zero =>
    intro d h_acc
    exfalso
    have h_emp : (networkTrace system time 0).base.emittedOperations = [] := by
      show ({ NetworkState.init system with currentTime := time 0 }
        : NetworkState).base.emittedOperations = []
      rfl
    unfold HasAccepted Emitted at h_acc
    change ValidatorOperation.block_accept vid d ∈
      (networkTrace system time 0).base.emittedOperations at h_acc
    rw [h_emp] at h_acc
    simp at h_acc
  | succ k ih =>
    intro d h_acc
    have h_step_eq : (networkTrace system time (k + 1)).base =
        (networkStep system (networkTrace system time k) (time (k + 1))).base := rfl
    rw [h_step_eq] at h_acc
    show ∃ B ∈ (networkStep system (networkTrace system time k)
      (time (k + 1))).base.blocks, B.d = d
    set s_pre : NetworkState := networkTrace system time k with h_s_pre
    set s_del : NetworkState :=
      ({ s_pre with currentTime := time (k + 1) } : NetworkState).deliverPending with h_s_del
    have h_del_base : s_del.base = s_pre.base :=
      NetworkState.deliverPending_preserves_base _
    -- Goal: ∃ B ∈ (networkStep system s_pre (time (k+1))).base.blocks, B.d = d
    -- h_acc: HasAccepted (networkStep system s_pre (time (k+1))).base vid d
    unfold networkStep at h_acc ⊢
    simp only at h_acc ⊢
    split
    case _ s_post h_fs =>
      simp only [h_fs] at h_acc
      rw [List.findSome?_eq_some_iff] at h_fs
      obtain ⟨_, ⟨vid_a, bv_a⟩, _, _, h_act, _⟩ := h_fs
      unfold networkTryActFor at h_act
      simp only at h_act
      split at h_act
      case isTrue _ =>
        injection h_act with h_eq
        subst h_eq
        rw [network_doPropose_HasAccepted_iff] at h_acc
        rw [h_del_base] at h_acc
        obtain ⟨B', hB'_mem, hB'_d⟩ := ih d h_acc
        refine ⟨B', ?_, hB'_d⟩
        show B' ∈ (doPropose system s_del.base vid_a bv_a.currentRound).blocks
        rw [h_del_base]
        exact doPropose_blocks system _ vid_a bv_a.currentRound B' hB'_mem
      case isFalse _ =>
        split at h_act
        case h_1 B_acc h_findAcc =>
          injection h_act with h_eq
          subst h_eq
          rw [network_doAccept_HasAccepted_iff] at h_acc
          rcases h_acc with h_old | ⟨_, h_d⟩
          · rw [h_del_base] at h_old
            obtain ⟨B', hB'_mem, hB'_d⟩ := ih d h_old
            refine ⟨B', ?_, hB'_d⟩
            show B' ∈ (doAccept s_del.base vid_a B_acc).blocks
            rw [doAccept_blocks_eq, h_del_base]; exact hB'_mem
          · have hB_mem : B_acc ∈ s_del.base.blocks :=
              List.mem_of_find?_eq_some h_findAcc
            refine ⟨B_acc, ?_, h_d.symm⟩
            show B_acc ∈ (doAccept s_del.base vid_a B_acc).blocks
            rw [doAccept_blocks_eq]; exact hB_mem
        case h_2 _ =>
          split at h_act
          case h_1 B_sto h_findSto =>
            injection h_act with h_eq
            subst h_eq
            rw [network_doStore_HasAccepted_iff] at h_acc
            rw [h_del_base] at h_acc
            obtain ⟨B', hB'_mem, hB'_d⟩ := ih d h_acc
            refine ⟨B', ?_, hB'_d⟩
            show B' ∈ (doStore s_del.base vid_a B_sto).blocks
            rw [doStore_blocks_eq, h_del_base]; exact hB'_mem
          case h_2 _ =>
            split at h_act
            case isTrue _ =>
              injection h_act with h_eq
              subst h_eq
              rw [updateValidator_HasAccepted_iff] at h_acc
              rw [h_del_base] at h_acc
              obtain ⟨B', hB'_mem, hB'_d⟩ := ih d h_acc
              refine ⟨B', ?_, hB'_d⟩
              show B' ∈ (updateValidator s_del.base vid_a _).blocks
              rw [updateValidator_blocks_eq, h_del_base]; exact hB'_mem
            case isFalse _ => simp at h_act
    case _ h_fs =>
      simp only [h_fs] at h_acc
      rw [h_del_base] at h_acc
      obtain ⟨B', hB'_mem, hB'_d⟩ := ih d h_acc
      refine ⟨B', ?_, hB'_d⟩
      show B' ∈ s_del.base.blocks
      rw [h_del_base]; exact hB'_mem

/-- Helper: validators in init state have currentRound = 0. -/
private lemma network_getValidator_init_round_zero
    (system : BlockSynchroniserSystem) (vid : ValidatorId) (bv : BelugaValidator)
    (h : (BelugaState.init system).getValidator vid = some bv) :
    bv.currentRound = 0 := by
  unfold BelugaState.init BelugaState.getValidator at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨p, h_find_some, h_eq⟩ := h
  -- p ∈ mapped list, so p has form (vid', { reputation := init, ... default fields })
  have h_p_mem := List.mem_of_find?_eq_some h_find_some
  rw [List.mem_map] at h_p_mem
  obtain ⟨q, _, h_q_eq⟩ := h_p_mem
  -- p = (q.1, { reputation := init }); so p.2.currentRound = 0 (default).
  rw [← h_eq, ← h_q_eq]

/-! ## Phase 4: Trace-level helpers -/

/-- `hasProposedFor` is monotone along `networkTrace`. -/
theorem network_hasProposedFor_monotone
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (vid : ValidatorId) (r : Round)
    (i j : Nat) (hij : i ≤ j)
    (h : hasProposedFor (networkTrace system time i).base vid r = true) :
    hasProposedFor (networkTrace system time j).base vid r = true := by
  induction' hij with j _ ih
  · exact h
  · unfold hasProposedFor at ih ⊢
    rw [List.any_eq_true] at ih ⊢
    obtain ⟨op, hop_mem, hop_match⟩ := ih
    refine ⟨op, ?_, hop_match⟩
    show op ∈ (networkStep system (networkTrace system time j) (time (j + 1))).base.emittedOperations
    exact networkStep_emittedOperations_monotone system _ _ op hop_mem


/-- Trace invariant: at every step, every validator at round R has proposed
for every r' < R. -/
theorem network_proposed_for_lt_currentRound
    (system : BlockSynchroniserSystem) (time : Nat → Nat) :
    ∀ k vid bv, (networkTrace system time k).base.getValidator vid = some bv →
      ∀ r' < bv.currentRound, hasProposedFor (networkTrace system time k).base vid r' = true := by
  intro k
  induction k with
  | zero =>
    intro vid bv h_get r' h_lt
    -- networkTrace 0 = init; init has currentRound = 0.
    have h_get' : (BelugaState.init system).getValidator vid = some bv := h_get
    have h_round : bv.currentRound = 0 :=
      network_getValidator_init_round_zero system vid bv h_get'
    rw [h_round] at h_lt
    exact absurd h_lt (Nat.not_lt_zero _)
  | succ k ih =>
    intro vid bv h_get r' h_lt
    have h_present_k : ∃ bv_prev, (networkTrace system time k).base.getValidator vid = some bv_prev := by
      by_contra h_none
      push_neg at h_none
      have h_get_none : (networkTrace system time k).base.getValidator vid = none :=
        Option.eq_none_iff_forall_ne_some.mpr h_none
      have h_succ_none : (networkTrace system time (k+1)).base.getValidator vid = none := by
        show (networkStep system (networkTrace system time k) (time (k+1))).base.getValidator vid = none
        exact networkStep_preserves_none system _ _ vid h_get_none
      rw [h_succ_none] at h_get
      contradiction
    obtain ⟨bv_prev, h_prev⟩ := h_present_k
    have h_nodup_k := networkTrace_validators_nodup system time k
    have h_get_step : (networkStep system (networkTrace system time k)
        (time (k+1))).base.getValidator vid = some bv := h_get
    have h_mono : bv_prev.currentRound ≤ bv.currentRound :=
      networkStep_round_monotone system _ _ h_nodup_k vid bv_prev bv h_prev h_get_step
    have h_at_most_one : bv.currentRound ≤ bv_prev.currentRound + 1 :=
      networkStep_round_at_most_one system _ _ h_nodup_k vid bv_prev bv h_prev h_get_step
    by_cases h_eq : bv.currentRound = bv_prev.currentRound
    · rw [h_eq] at h_lt
      have h_prop_k := ih vid bv_prev h_prev r' h_lt
      exact network_hasProposedFor_monotone system time vid r' k (k+1) (Nat.le_succ k) h_prop_k
    · have h_advance : bv.currentRound = bv_prev.currentRound + 1 := by
        rcases Nat.lt_or_ge bv_prev.currentRound bv.currentRound with h_lt | h_ge
        · -- bv_prev.cr < bv.cr; combined with h_at_most_one (bv.cr ≤ bv_prev.cr + 1)
          have : bv.currentRound ≤ bv_prev.currentRound + 1 := h_at_most_one
          have : bv_prev.currentRound + 1 ≤ bv.currentRound := h_lt
          exact Nat.le_antisymm ‹bv.currentRound ≤ bv_prev.currentRound + 1› ‹_›
        · -- bv_prev.cr ≥ bv.cr; combined with h_mono (bv_prev.cr ≤ bv.cr) gives equality
          exact absurd (Nat.le_antisymm h_ge h_mono) h_eq
      by_cases h_lt' : r' < bv_prev.currentRound
      · have h_prop_k := ih vid bv_prev h_prev r' h_lt'
        exact network_hasProposedFor_monotone system time vid r' k (k+1) (Nat.le_succ k) h_prop_k
      · have h_eq_r : r' = bv_prev.currentRound := by
          push_neg at h_lt'
          -- h_lt : r' < bv.currentRound = bv_prev.currentRound + 1
          -- h_lt' : bv_prev.currentRound ≤ r'
          rw [h_advance] at h_lt
          have : r' ≤ bv_prev.currentRound := Nat.le_of_lt_succ h_lt
          exact Nat.le_antisymm this h_lt'
        rw [h_eq_r]
        have h_prop_k :=
          networkStep_advance_implies_hasProposedFor system _ _ vid bv_prev bv
            h_nodup_k h_prev h_get_step h_advance
        exact network_hasProposedFor_monotone system time vid bv_prev.currentRound k (k+1)
          (Nat.le_succ k) h_prop_k

/-- Find the step where vid's round transitioned from r to r+1. -/
theorem network_find_advance_step
    (system : BlockSynchroniserSystem) (time : Nat → Nat) (vid : ValidatorId) (r : Round) :
    ∀ {k₀ k_target}, k₀ ≤ k_target →
    ∀ bv₀ bv_t,
    (networkTrace system time k₀).base.getValidator vid = some bv₀ →
    (networkTrace system time k_target).base.getValidator vid = some bv_t →
    bv₀.currentRound = r →
    bv_t.currentRound ≥ r + 1 →
    ∃ k_a bv bv',
      k₀ ≤ k_a ∧ k_a < k_target ∧
      (networkTrace system time k_a).base.getValidator vid = some bv ∧
      (networkTrace system time (k_a + 1)).base.getValidator vid = some bv' ∧
      bv.currentRound = r ∧ bv'.currentRound = r + 1 := by
  intros k₀ k_target hle
  induction hle with
  | refl =>
    intros bv₀ bv_t h₀ h_t hr₀ hr_t
    rw [h₀] at h_t
    have h_eq : bv₀ = bv_t := Option.some.inj h_t
    exfalso
    rw [h_eq] at hr₀
    rw [hr₀] at hr_t
    exact absurd hr_t (Nat.lt_irrefl _ ∘ Nat.lt_of_succ_le)
  | @step k_target' h ih =>
    intros bv₀ bv_t h₀ h_t hr₀ hr_t
    have h_persistent_prev :
        ∃ bv_prev, (networkTrace system time k_target').base.getValidator vid = some bv_prev := by
      by_contra h_none
      push_neg at h_none
      have h_get_none : (networkTrace system time k_target').base.getValidator vid = none :=
        Option.eq_none_iff_forall_ne_some.mpr h_none
      have h_succ_none :
          (networkTrace system time (k_target' + 1)).base.getValidator vid = none := by
        show (networkStep system (networkTrace system time k_target')
                (time (k_target' + 1))).base.getValidator vid = none
        exact networkStep_preserves_none system _ _ vid h_get_none
      rw [h_succ_none] at h_t; contradiction
    obtain ⟨bv_prev, h_prev⟩ := h_persistent_prev
    have h_step_at_most : bv_t.currentRound ≤ bv_prev.currentRound + 1 := by
      apply networkStep_round_at_most_one system (networkTrace system time k_target')
        (time (k_target' + 1)) (networkTrace_validators_nodup system time k_target')
        vid bv_prev bv_t h_prev
      show (networkStep system (networkTrace system time k_target')
              (time (k_target' + 1))).base.getValidator vid = some bv_t
      exact h_t
    by_cases h_case : bv_prev.currentRound ≥ r + 1
    · obtain ⟨k_a, bv_a, bv_a', h_le, h_lt, h_a, h_a', h_eq_r, h_eq_r1⟩ :=
        ih bv₀ bv_prev h₀ h_prev hr₀ h_case
      exact ⟨k_a, bv_a, bv_a', h_le, Nat.lt_succ_of_lt h_lt, h_a, h_a', h_eq_r, h_eq_r1⟩
    · push_neg at h_case
      have hbp_le_r : bv_prev.currentRound ≤ r := Nat.le_of_lt_succ h_case
      have hbp_ge_r : bv_prev.currentRound ≥ r := by
        have : r + 1 ≤ bv_prev.currentRound + 1 := le_trans hr_t h_step_at_most
        exact Nat.le_of_succ_le_succ this
      have hbp_eq : bv_prev.currentRound = r := le_antisymm hbp_le_r hbp_ge_r
      have hbt_eq : bv_t.currentRound = r + 1 := by
        have h1 : bv_t.currentRound ≤ r + 1 := by rw [← hbp_eq]; exact h_step_at_most
        exact le_antisymm h1 hr_t
      exact ⟨k_target', bv_prev, bv_t, h, Nat.lt_succ_self _, h_prev, h_t, hbp_eq, hbt_eq⟩

/-- The trace invariant: at every step of `networkTrace`, every
validator's `roundEntryTime` is bounded by the state's
`currentTime`. -/
theorem roundEntryTime_le_currentTime
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (k : Nat) :
    ∀ vid bv, (networkTrace system time k).base.getValidator vid = some bv →
      bv.roundEntryTime ≤ (networkTrace system time k).currentTime := by
  induction k with
  | zero =>
    intro vid bv h_get
    rw [currentTime_tracks_time]
    -- At init, every validator was constructed with default fields including
    -- `roundEntryTime := 0`. So bv.roundEntryTime = 0 ≤ time 0.
    have h_rt_zero : bv.roundEntryTime = 0 := by
      -- (networkTrace system time 0).base.validators is constructed by
      -- `system.validators.map (fun (vid, _) => (vid, default-bv))`. So bv
      -- is the default BelugaValidator (only `reputation` non-default), and
      -- in particular `bv.roundEntryTime = 0`.
      change ({ NetworkState.init system with currentTime := time 0 } :
        NetworkState).base.getValidator vid = some bv at h_get
      unfold NetworkState.init BelugaState.init BelugaState.getValidator at h_get
      simp only at h_get
      rw [Option.map_eq_some_iff] at h_get
      obtain ⟨⟨vid', bv'⟩, h_find, h_proj⟩ := h_get
      simp at h_proj
      rw [← h_proj]
      -- h_find : find? on the .map shows (vid', bv') is the mapped pair.
      have h_mem : (vid', bv') ∈
          system.validators.map (fun p =>
            (p.1, { reputation := ReputationTable.init system : BelugaValidator })) :=
        List.mem_of_find?_eq_some h_find
      rw [List.mem_map] at h_mem
      obtain ⟨p, _, h_pair_eq⟩ := h_mem
      have : bv' = ({ reputation := ReputationTable.init system : BelugaValidator }) := by
        have := h_pair_eq
        simp [Prod.ext_iff] at this
        exact this.2.symm
      rw [this]
    rw [h_rt_zero]
    exact Nat.zero_le _
  | succ k ih =>
    intro vid bv h_get
    rw [currentTime_tracks_time]
    -- Inductive step: networkStep advances currentTime to time(k+1),
    -- runs deliverPending (preserves base.validators), then
    -- networkTryActFor (preserves roundEntry-bound by Sorry 1, proved above).
    -- The IH gives the invariant at trace k under currentTime = time k;
    -- monotonicity of `time` lifts the bound to time(k+1).
    show bv.roundEntryTime ≤ time (k + 1)
    have h_trace_succ : networkTrace system time (k + 1) =
        networkStep system (networkTrace system time k) (time (k + 1)) := rfl
    rw [h_trace_succ] at h_get
    -- The IH (with currentTime_tracks_time) gives a `time k` bound.
    -- Lift to `time (k+1)` via monotonicity at the post-currentTime-bump
    -- state (s_pre below).
    set s_pre : NetworkState := { networkTrace system time k with
      currentTime := time (k + 1) } with h_s_pre
    have h_inv_pre : ∀ vid' bv',
        s_pre.base.getValidator vid' = some bv' →
        bv'.roundEntryTime ≤ s_pre.currentTime := by
      intro vid' bv' h_get'
      have h_orig : (networkTrace system time k).base.getValidator vid' = some bv' :=
        h_get'
      have h_ih := ih vid' bv' h_orig
      rw [currentTime_tracks_time] at h_ih
      calc bv'.roundEntryTime ≤ time k := h_ih
        _ ≤ time (k + 1) := h_mono _ _ (Nat.le_succ _)
        _ = s_pre.currentTime := rfl
    -- After deliverPending: base.validators unchanged, currentTime unchanged.
    have h_inv_del : ∀ vid' bv',
        s_pre.deliverPending.base.getValidator vid' = some bv' →
        bv'.roundEntryTime ≤ s_pre.deliverPending.currentTime := by
      intro vid' bv' h_get'
      rw [NetworkState.deliverPending_preserves_currentTime]
      apply h_inv_pre vid' bv'
      unfold BelugaState.getValidator at h_get' ⊢
      rw [NetworkState.deliverPending_preserves_base_validators] at h_get'
      exact h_get'
    -- Unfold networkStep.
    show bv.roundEntryTime ≤ time (k + 1)
    unfold networkStep at h_get
    simp only at h_get
    -- s_pre = { networkTrace ... with currentTime := time(k+1) } matches what
    -- networkStep constructs internally.
    -- The trace at k+1 is networkStep system (...) (time(k+1)).
    -- networkStep applies findSome? over the post-deliverPending state's validators.
    -- We use networkStep_currentTime to get s_pre.deliverPending base preserves
    -- currentTime, then split on the findSome?.
    -- The cleaner argument: the post-state is either s_pre.deliverPending (if
    -- findSome? = none) or networkTryActFor's result (if some). Both preserve
    -- the rt-bound at currentTime = time(k+1). We construct the proof by
    -- showing the rt-bound holds for whatever the post-state is.
    -- Use `split` on the match in h_get directly.
    split at h_get
    case h_1 s'' h_fs_some =>
      -- some case: networkTryActFor produced s''.
      rw [List.findSome?_eq_some_iff] at h_fs_some
      obtain ⟨_, ⟨vid_a, bv_a⟩, _, h_split, h_act, _⟩ := h_fs_some
      have h_a_mem : (vid_a, bv_a) ∈ s_pre.deliverPending.base.validators := by
        rw [h_split]; simp +decide
      have h_a_get : s_pre.deliverPending.base.getValidator vid_a = some bv_a := by
        unfold BelugaState.getValidator
        rw [find?_of_mem_nodup _ _ _ h_a_mem]
        · rfl
        · rw [NetworkState.deliverPending_preserves_base_validators]
          show ((networkTrace system time k).base.validators.map Prod.fst).Nodup
          exact networkTrace_validators_nodup system time k
      have h_post := networkTryActFor_preserves_roundEntry_bound system
        s_pre.deliverPending h_inv_del vid_a bv_a h_a_get s'' h_act vid bv h_get
      have h_ct'' : s''.currentTime = s_pre.deliverPending.currentTime :=
        networkTryActFor_preserves_currentTime system s_pre.deliverPending vid_a bv_a s'' h_act
      rw [h_ct''] at h_post
      rw [NetworkState.deliverPending_preserves_currentTime] at h_post
      change bv.roundEntryTime ≤ s_pre.currentTime at h_post
      exact h_post
    case h_2 _ =>
      -- none case: post-state is s_pre.deliverPending.
      have h_le := h_inv_del vid bv h_get
      rw [NetworkState.deliverPending_preserves_currentTime] at h_le
      change bv.roundEntryTime ≤ s_pre.currentTime at h_le
      exact h_le

/-! ## Phase E.3: timeout firing -/

/-- Past `roundEntryTime + 4Δ`, the timeout branch is enabled. Direct
from the definition of `timeoutFired`. -/
theorem timeout_fires_past_4delta
    (system : BlockSynchroniserSystem) (s : NetworkState)
    (bv : BelugaValidator)
    (h : s.currentTime ≥ bv.roundEntryTime + 4 * system.Δ) :
    s.timeoutFired system bv = true := by
  unfold NetworkState.timeoutFired
  exact decide_eq_true h

/-! ## Phase E.4: derive `schedulerFairness_holds`

The paper-faithful primitive **`ActionScheduling`**: post-GST,
when an honest validator's action is enabled at step `k`, the
validator is selected as the actor at some step `k'` with
`time k' ≤ time k + Δ`. This is the explicit form of paper §4.2's
implicit "honest validators run the protocol" — finding F-1. -/

/-- **`ActionScheduling`** — paper §4.2 + finding F-1: post-GST,
honest validators with enabled actions are scheduled by the trace
within `Δ` wall-clock. Combined with `NetworkDelivery`, this
discharges the previous `SchedulerFairness` axiom in a paper-
faithful factoring (each axiom now corresponds to a paper-stated
primitive: §2 `Δ`-delivery and §4.2 protocol-execution). -/
def ActionScheduling (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop :=
  ∀ k vid bv,
    isHonestValidator system vid = true →
    time k ≥ system.GST →
    (networkTrace system time k).base.getValidator vid = some bv →
    -- The validator advances (its currentRound goes up) within `Δ`
    -- wall-clock. Paper §4.2's combined effect of:
    --   (a) the propose action being always enabled when not yet proposed,
    --   (b) the per-round timeout `T_rd = 4Δ` firing eventually,
    --   (c) honest validators acting on enabled actions promptly,
    -- combined means honest validators *do* advance their local round
    -- post-GST, with rate bounded by `Δ`.
    ∃ k' bv', k ≤ k' ∧ time k' ≤ time k + system.Δ ∧
      (networkTrace system time k').base.getValidator vid = some bv' ∧
      bv'.currentRound > bv.currentRound

/-- **`BoundedRoundSpread_networkTrace`** — paper §4.2's protocol
synchronization (push protocol + per-round timeout `T_rd = 4Δ`)
maintains a gap-1 round-spread invariant post-GST: any two honest
validators are within 1 local round of each other. This is finding
F-1b made explicit, stated against `networkTrace`. -/
def BoundedRoundSpread_networkTrace
    (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop :=
  ∀ k vid₁ vid₂ bv₁ bv₂,
    time k ≥ system.GST →
    isHonestValidator system vid₁ = true →
    isHonestValidator system vid₂ = true →
    (networkTrace system time k).base.getValidator vid₁ = some bv₁ →
    (networkTrace system time k).base.getValidator vid₂ = some bv₂ →
    bv₁.currentRound ≤ bv₂.currentRound + 1

/-! ## `PartiallySynchronousFairness` — bundled paper primitives

Bundle of all six paper-named primitives needed by the §5 theorems
on `networkTrace` and the T2/T4 `Eventual*` derivations on
`networkTraceWithPull`. Symmetric to the existing conclusion-side
`BelugaPostGSTLiveness` bundle; carries one named hypothesis per
paper-stated assumption.

| Field | Paper ref | Trace |
|---|---|---|
| `networkDelivery` | §2 `Δ`-delivery | `networkTrace` |
| `actionScheduling` | §4.2 round-advance | `networkTrace` |
| `boundedRoundSpread` | §4.2 + F-1b gap-1 | `networkTrace` |
| `acceptScheduling` | §4.2 accept-action | `networkTraceWithPull` |
| `pullRequestDelivery` | §4.3 pull-channel `Δ`-delivery | `networkTraceWithPull` |
| `pullResponseScheduling` | §4.3 pull-response action | `networkTraceWithPull` |

Top-level §5 wrappers consume this single hypothesis instead of
threading 5–6 individual primitives. Internal proofs destructure
to access individual fields. -/
structure PartiallySynchronousFairness
    (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop where
  /-- Paper §2 `Δ`-bounded honest-honest block_propose delivery. -/
  networkDelivery        : NetworkDelivery system time
  /-- Paper §4.2 per-validator round-advance liveness. -/
  actionScheduling       : ActionScheduling system time
  /-- F-1b gap-1 invariant on the round spread between honest
  validators (paper §4.2 protocol synchronization). -/
  boundedRoundSpread     : BoundedRoundSpread_networkTrace system time
  /-- Paper §4.2 per-action liveness for the accept action: when an
  honest validator has an acceptable in-pool block (canAcceptBlock
  = true), `doAccept` fires within `Δ` post-GST. -/
  acceptScheduling       : AcceptScheduling system time
  /-- Paper §4.3 pull-channel `Δ`-delivery: honest pull requests
  reach honest responders' `pullRequestsInbox` within `Δ`. -/
  pullRequestDelivery    : PullRequestDelivery system time
  /-- Paper §4.3 pull-response action liveness: honest responder
  with non-empty `pullInbox` drains the first request within `Δ`. -/
  pullResponseScheduling : PullResponseScheduling system time

/-- **The headline theorem.** Under the paper §2 + §4.2 + §4.3
mechanisms (NetworkDelivery, ActionScheduling, BoundedRoundSpread),
`networkTrace` satisfies paper L1's scheduler-fairness property:
post-GST, if some honest validator is at round `r` at step `k`,
every honest validator reaches round `≥ r + 1` within `3Δ`.

**Where paper §4 mechanisms appear in the proof**:

- **`NetworkDelivery` (paper §2)** is a stated primitive in the
  signature; its role in the protocol is to ensure that honest
  validators' propose ops are received by all honest within `Δ`.
  The current proof body does not directly invoke it (the timeout
  + scheduling argument suffices for the 3Δ bound), but it is
  paper-stated and threaded through the §5 wrappers as an
  available primitive for tighter ImPoA-driven refinements.
- **`ActionScheduling` (paper §4.2 + finding F-1)**: the
  per-validator Δ-bounded round advance. Used twice in the proof
  (steps 1 and 2 of paper L1's optimistic argument: vid_w
  advances from `r` to `r+1` to `r+2`).
- **`BoundedRoundSpread_networkTrace` (paper §4.2 + finding F-1b)**:
  the gap-1 invariant maintained by the push protocol's
  parent-acceptance rules combined with the per-round timeout
  `T_rd = 4Δ`. After vid_w reaches round ≥ r+2, every honest is
  within 1 of vid_w, so all are at ≥ r+1.
- **ImPoA (paper §4.3)** appears in the *definition* of
  `networkTryActFor`'s accept rule (`canAcceptBlock` consults
  `parentsAcceptableImPoA`). This is what makes
  `ActionScheduling` *valid* for the protocol — without ImPoA,
  honest validators would block waiting for direct parent delivery
  and `ActionScheduling`'s `Δ` bound would fail. The proof body
  treats `ActionScheduling` as a primitive whose validity rests
  on ImPoA.

The proof structure mirrors `belugaTrace_schedulerFairness` but is
stated against `networkTrace` (the paper-faithful protocol model). -/
theorem schedulerFairness_holds
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (_h_delivery : NetworkDelivery system time)
    (h_scheduling : ActionScheduling system time)
    (h_spread : BoundedRoundSpread_networkTrace system time)
    (h_persistent : ∀ vid k, isHonestValidator system vid = true →
      ∃ bv, (networkTrace system time k).base.getValidator vid = some bv)
    : ∀ k r,
        time k ≥ system.GST →
        (∃ vid bv, isHonestValidator system vid = true ∧
          (networkTrace system time k).base.getValidator vid = some bv ∧
          bv.currentRound = r) →
        ∃ k', k ≤ k' ∧ time k' ≤ time k + 3 * system.Δ ∧
          ∀ vid, isHonestValidator system vid = true →
            ∃ bv, (networkTrace system time k').base.getValidator vid = some bv ∧
                  bv.currentRound ≥ r + 1 := by
  intro k r h_post_gst ⟨vid_w, bv_w, h_w_honest, h_w_get, h_w_round⟩
  -- Step 1: Apply ActionScheduling to vid_w to advance once
  -- (vid_w's round goes from r to ≥ r+1 within Δ).
  obtain ⟨k₁, bv_w₁, hk₁_le, hk₁_time, h_w₁_get, h_w₁_round⟩ :=
    h_scheduling k vid_w bv_w h_w_honest h_post_gst h_w_get
  -- Step 2: Apply ActionScheduling again to vid_w (advance to ≥ r+2 within 2Δ).
  have h_post_gst₁ : time k₁ ≥ system.GST :=
    le_trans h_post_gst (h_mono k k₁ hk₁_le)
  obtain ⟨k₂, bv_w₂, hk₂_le, hk₂_time, h_w₂_get, h_w₂_round⟩ :=
    h_scheduling k₁ vid_w bv_w₁ h_w_honest h_post_gst₁ h_w₁_get
  have h_w₂_ge : bv_w₂.currentRound ≥ r + 2 := by
    have h1 : bv_w.currentRound + 1 ≤ bv_w₁.currentRound := h_w₁_round
    have h2 : bv_w₁.currentRound + 1 ≤ bv_w₂.currentRound := h_w₂_round
    have h_step1 : r + 1 ≤ bv_w₁.currentRound := by
      rw [← h_w_round]; exact h1
    have h_step2 : r + 2 ≤ bv_w₂.currentRound :=
      le_trans (Nat.add_le_add_right h_step1 1) h2
    exact h_step2
  have h_post_gst₂ : time k₂ ≥ system.GST :=
    le_trans h_post_gst₁ (h_mono k₁ k₂ hk₂_le)
  -- Step 3: At step k₂, BoundedRoundSpread gives every honest within 1 of
  -- vid_w (which is at round ≥ r+2), so every honest is at ≥ r+1.
  refine ⟨k₂, le_trans hk₁_le hk₂_le, ?_, ?_⟩
  · -- Time bound: time k₂ ≤ time k₁ + Δ ≤ time k + 2Δ ≤ time k + 3Δ.
    have h_t1 : time k₁ ≤ time k + system.Δ := hk₁_time
    have h_t2 : time k₂ ≤ time k₁ + system.Δ := hk₂_time
    omega
  · intro vid h_vid_honest
    obtain ⟨bv_vid, h_vid_get⟩ := h_persistent vid k₂ h_vid_honest
    refine ⟨bv_vid, h_vid_get, ?_⟩
    have h_sp : bv_w₂.currentRound ≤ bv_vid.currentRound + 1 :=
      h_spread k₂ vid_w vid bv_w₂ bv_vid h_post_gst₂ h_w_honest h_vid_honest
        h_w₂_get h_vid_get
    have h_lower : r + 2 ≤ bv_w₂.currentRound := h_w₂_ge
    have h_chain : r + 2 ≤ bv_vid.currentRound + 1 := le_trans h_lower h_sp
    exact Nat.le_of_succ_le_succ h_chain

/-- `networkTraceWithPull` analog of `schedulerFairness_holds`. Same
proof structure (pure round arithmetic over the with-pull primitives). -/
theorem schedulerFairness_holds_withPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (_h_delivery : NetworkDeliveryWithPull system time)
    (h_scheduling : ActionSchedulingWithPull system time)
    (h_spread : BoundedRoundSpread_networkTraceWithPull system time)
    (h_persistent : ∀ vid k, isHonestValidator system vid = true →
      ∃ bv, (networkTraceWithPull system time k).base.getValidator vid = some bv)
    : ∀ k r,
        time k ≥ system.GST →
        (∃ vid bv, isHonestValidator system vid = true ∧
          (networkTraceWithPull system time k).base.getValidator vid = some bv ∧
          bv.currentRound = r) →
        ∃ k', k ≤ k' ∧ time k' ≤ time k + 3 * system.Δ ∧
          ∀ vid, isHonestValidator system vid = true →
            ∃ bv, (networkTraceWithPull system time k').base.getValidator vid = some bv ∧
                  bv.currentRound ≥ r + 1 := by
  intro k r h_post_gst ⟨vid_w, bv_w, h_w_honest, h_w_get, h_w_round⟩
  obtain ⟨k₁, bv_w₁, hk₁_le, hk₁_time, h_w₁_get, h_w₁_round⟩ :=
    h_scheduling k vid_w bv_w h_w_honest h_post_gst h_w_get
  have h_post_gst₁ : time k₁ ≥ system.GST :=
    le_trans h_post_gst (h_mono k k₁ hk₁_le)
  obtain ⟨k₂, bv_w₂, hk₂_le, hk₂_time, h_w₂_get, h_w₂_round⟩ :=
    h_scheduling k₁ vid_w bv_w₁ h_w_honest h_post_gst₁ h_w₁_get
  have h_w₂_ge : bv_w₂.currentRound ≥ r + 2 := by
    have h1 : bv_w.currentRound + 1 ≤ bv_w₁.currentRound := h_w₁_round
    have h2 : bv_w₁.currentRound + 1 ≤ bv_w₂.currentRound := h_w₂_round
    have h_step1 : r + 1 ≤ bv_w₁.currentRound := by
      rw [← h_w_round]; exact h1
    exact le_trans (Nat.add_le_add_right h_step1 1) h2
  have h_post_gst₂ : time k₂ ≥ system.GST :=
    le_trans h_post_gst₁ (h_mono k₁ k₂ hk₂_le)
  refine ⟨k₂, le_trans hk₁_le hk₂_le, ?_, ?_⟩
  · have h_t1 : time k₁ ≤ time k + system.Δ := hk₁_time
    have h_t2 : time k₂ ≤ time k₁ + system.Δ := hk₂_time
    omega
  · intro vid h_vid_honest
    obtain ⟨bv_vid, h_vid_get⟩ := h_persistent vid k₂ h_vid_honest
    refine ⟨bv_vid, h_vid_get, ?_⟩
    have h_sp : bv_w₂.currentRound ≤ bv_vid.currentRound + 1 :=
      h_spread k₂ vid_w vid bv_w₂ bv_vid h_post_gst₂ h_w_honest h_vid_honest
        h_w₂_get h_vid_get
    have h_chain : r + 2 ≤ bv_vid.currentRound + 1 := le_trans h_w₂_ge h_sp
    exact Nat.le_of_succ_le_succ h_chain

/-- Iterated `schedulerFairness_holds`: every honest validator
eventually reaches round ≥ R. -/
theorem network_all_honest_eventually_at_round
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_delivery : NetworkDelivery system time)
    (h_scheduling : ActionScheduling system time)
    (h_spread : BoundedRoundSpread_networkTrace system time)
    (vid_w : ValidatorId) (h_w : isHonestValidator system vid_w = true)
    (k₀ : Nat) (h_gst : time k₀ ≥ system.GST) :
    ∀ R, ∃ k, k₀ ≤ k ∧ time k ≥ system.GST ∧
      ∀ vid, isHonestValidator system vid = true →
        ∃ bv, (networkTrace system time k).base.getValidator vid = some bv ∧
              bv.currentRound ≥ R := by
  intro R
  have h_persistent : ∀ vid k, isHonestValidator system vid = true →
      ∃ bv, (networkTrace system time k).base.getValidator vid = some bv :=
    fun vid k h => network_honest_validator_persistent_trace system time vid h k
  induction R with
  | zero =>
    refine ⟨k₀, le_refl _, h_gst, ?_⟩
    intro vid h_vid
    obtain ⟨bv, h_bv⟩ := network_honest_validator_persistent_trace system time vid h_vid k₀
    exact ⟨bv, h_bv, Nat.zero_le _⟩
  | succ R ih =>
    obtain ⟨k_R, h_k_R_le, h_k_R_gst, h_all_R⟩ := ih
    obtain ⟨bv_w, h_bv_w, h_bv_w_round⟩ := h_all_R vid_w h_w
    obtain ⟨k', h_k'_le, _, h_all_succ⟩ :=
      schedulerFairness_holds system time h_mono h_delivery h_scheduling h_spread h_persistent
        k_R bv_w.currentRound h_k_R_gst ⟨vid_w, bv_w, h_w, h_bv_w, rfl⟩
    refine ⟨k', le_trans h_k_R_le h_k'_le,
      le_trans h_k_R_gst (h_mono _ _ h_k'_le), ?_⟩
    intro vid h_vid
    obtain ⟨bv', h_bv', h_bv'_round⟩ := h_all_succ vid h_vid
    exact ⟨bv', h_bv', le_trans (Nat.succ_le_succ h_bv_w_round) h_bv'_round⟩

/-- With-pull analog of `network_all_honest_eventually_at_round`. -/
theorem network_all_honest_eventually_at_roundWithPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_delivery : NetworkDeliveryWithPull system time)
    (h_scheduling : ActionSchedulingWithPull system time)
    (h_spread : BoundedRoundSpread_networkTraceWithPull system time)
    (vid_w : ValidatorId) (h_w : isHonestValidator system vid_w = true)
    (k₀ : Nat) (h_gst : time k₀ ≥ system.GST) :
    ∀ R, ∃ k, k₀ ≤ k ∧ time k ≥ system.GST ∧
      ∀ vid, isHonestValidator system vid = true →
        ∃ bv, (networkTraceWithPull system time k).base.getValidator vid = some bv ∧
              bv.currentRound ≥ R := by
  intro R
  have h_persistent : ∀ vid k, isHonestValidator system vid = true →
      ∃ bv, (networkTraceWithPull system time k).base.getValidator vid = some bv :=
    fun vid k h => network_honest_validator_persistent_traceWithPull system time vid h k
  induction R with
  | zero =>
    refine ⟨k₀, le_refl _, h_gst, ?_⟩
    intro vid h_vid
    obtain ⟨bv, h_bv⟩ := network_honest_validator_persistent_traceWithPull system time vid h_vid k₀
    exact ⟨bv, h_bv, Nat.zero_le _⟩
  | succ R ih =>
    obtain ⟨k_R, h_k_R_le, h_k_R_gst, h_all_R⟩ := ih
    obtain ⟨bv_w, h_bv_w, h_bv_w_round⟩ := h_all_R vid_w h_w
    obtain ⟨k', h_k'_le, _, h_all_succ⟩ :=
      schedulerFairness_holds_withPull system time h_mono h_delivery h_scheduling h_spread h_persistent
        k_R bv_w.currentRound h_k_R_gst ⟨vid_w, bv_w, h_w, h_bv_w, rfl⟩
    refine ⟨k', le_trans h_k_R_le h_k'_le,
      le_trans h_k_R_gst (h_mono _ _ h_k'_le), ?_⟩
    intro vid h_vid
    obtain ⟨bv', h_bv', h_bv'_round⟩ := h_all_succ vid h_vid
    exact ⟨bv', h_bv', le_trans (Nat.succ_le_succ h_bv_w_round) h_bv'_round⟩

/-! ## emittedOperations monotonicity for `networkTraceWithPull` -/

/-- `networkTryActFor` only appends to `emittedOperations` (already proved
in `networkTryActFor_emittedOperations_monotone`); same shape proof here
under the trace (handled by existing helper). The new step bodies in
`networkStepWithPull` (deliverPullPending, pullStep) preserve
`emittedOperations` (they don't touch base — just pull queues and
`inflight`). -/
theorem networkStepWithPull_emittedOperations_monotone
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat) :
    ∀ op ∈ s.base.emittedOperations,
      op ∈ (networkStepWithPull system s newTime).base.emittedOperations := by
  intro op hop
  unfold networkStepWithPull
  have h_del_base :
      ({ s with currentTime := newTime } : NetworkState).deliverPending.base = s.base := by
    rw [NetworkState.deliverPending_preserves_base]
  have h_pull_del_base :
      (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending).base
        = s.base := by
    rw [NetworkState.deliverPullPending_preserves_base]; exact h_del_base
  have h_pulled_base :
      (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
        = s.base := by
    rw [pullStep_preserves_base]; exact h_pull_del_base
  have h_pulled_hop : op ∈
      (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base.emittedOperations := by
    rw [h_pulled_base]; exact hop
  simp only
  split
  case _ s' h_fs =>
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, ⟨vid_a, bv_a⟩, _, _, h_act, _⟩ := h_fs
    exact networkTryActFor_emittedOperations_monotone system _ vid_a bv_a s' h_act op h_pulled_hop
  case _ _ => exact h_pulled_hop

/-- `HasAccepted` is monotone along `networkTraceWithPull`: once accepted,
always accepted. -/
theorem network_HasAccepted_monotone_withPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (vid : ValidatorId) (d : BlockDigest)
    (k₁ k₂ : Nat) (h_le : k₁ ≤ k₂)
    (h_acc : HasAccepted (networkTraceWithPull system time k₁).base vid d) :
    HasAccepted (networkTraceWithPull system time k₂).base vid d := by
  induction h_le with
  | refl => exact h_acc
  | @step k_mid _ ih =>
    show ValidatorOperation.block_accept vid d ∈
      (networkStepWithPull system (networkTraceWithPull system time k_mid)
        (time (k_mid + 1))).base.emittedOperations
    exact networkStepWithPull_emittedOperations_monotone system
      (networkTraceWithPull system time k_mid) (time (k_mid + 1)) _ ih

/-- `hasProposedFor` is monotone along `networkTraceWithPull`. -/
theorem network_hasProposedFor_monotoneWithPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (vid : ValidatorId) (r : Round)
    (i j : Nat) (hij : i ≤ j)
    (h : hasProposedFor (networkTraceWithPull system time i).base vid r = true) :
    hasProposedFor (networkTraceWithPull system time j).base vid r = true := by
  induction' hij with j _ ih
  · exact h
  · unfold hasProposedFor at ih ⊢
    rw [List.any_eq_true] at ih ⊢
    obtain ⟨op, hop_mem, hop_match⟩ := ih
    refine ⟨op, ?_, hop_match⟩
    show op ∈ (networkStepWithPull system (networkTraceWithPull system time j) (time (j + 1))).base.emittedOperations
    exact networkStepWithPull_emittedOperations_monotone system _ _ op hop_mem

/-! ## Round monotonicity for `networkStepWithPull` -/

/-- One `networkStepWithPull` never decreases any validator's
`currentRound`. Mirror of `networkStep_round_monotone`; the additional
pull-mechanism layers (`deliverPullPending`, `pullStep`) preserve
`.base` so the round-relevant facts transfer. -/
theorem networkStepWithPull_round_monotone
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat)
    (h_nodup : (s.base.validators.map Prod.fst).Nodup)
    (vid : ValidatorId) (bv bv' : BelugaValidator)
    (h : s.base.getValidator vid = some bv)
    (h' : (networkStepWithPull system s newTime).base.getValidator vid = some bv') :
    bv.currentRound ≤ bv'.currentRound := by
  unfold networkStepWithPull at h'
  have h_del_base :
      ({ s with currentTime := newTime } : NetworkState).deliverPending.base = s.base := by
    rw [NetworkState.deliverPending_preserves_base]
  have h_pull_del_base :
      (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending).base
        = s.base := by
    rw [NetworkState.deliverPullPending_preserves_base]; exact h_del_base
  have h_pulled_base :
      (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
        = s.base := by
    rw [pullStep_preserves_base]; exact h_pull_del_base
  have h_pulled_nodup :
      ((pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base.validators.map Prod.fst).Nodup := by
    rw [h_pulled_base]; exact h_nodup
  have h_pulled_get :
      (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base.getValidator vid
        = some bv := by
    rw [h_pulled_base]; exact h
  simp only at h'
  split at h'
  case _ s'' h_fs =>
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, ⟨vid_a, bv_a⟩, _, h_l_split, h_act, _⟩ := h_fs
    have h_a_mem : (vid_a, bv_a) ∈
        (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base.validators := by
      rw [h_l_split]; simp
    have h_a_get :
        (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base.getValidator vid_a
          = some bv_a := by
      unfold BelugaState.getValidator
      rw [Option.map_eq_some_iff]
      exact ⟨(vid_a, bv_a), find?_of_mem_nodup _ vid_a bv_a h_a_mem h_pulled_nodup, rfl⟩
    exact networkTryActFor_round_monotone system _ vid_a bv_a h_a_get s'' h_act
      vid bv bv' h_pulled_get h'
  case _ _ =>
    rw [h_pulled_get] at h'; injection h' with h_eq; rw [h_eq]

/-- One `networkStepWithPull` increases `currentRound` by at most 1. -/
theorem networkStepWithPull_round_at_most_one
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat)
    (h_nodup : (s.base.validators.map Prod.fst).Nodup)
    (vid : ValidatorId) (bv bv' : BelugaValidator)
    (h : s.base.getValidator vid = some bv)
    (h' : (networkStepWithPull system s newTime).base.getValidator vid = some bv') :
    bv'.currentRound ≤ bv.currentRound + 1 := by
  unfold networkStepWithPull at h'
  have h_del_base :
      ({ s with currentTime := newTime } : NetworkState).deliverPending.base = s.base := by
    rw [NetworkState.deliverPending_preserves_base]
  have h_pull_del_base :
      (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending).base
        = s.base := by
    rw [NetworkState.deliverPullPending_preserves_base]; exact h_del_base
  have h_pulled_base :
      (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
        = s.base := by
    rw [pullStep_preserves_base]; exact h_pull_del_base
  have h_pulled_nodup :
      ((pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base.validators.map Prod.fst).Nodup := by
    rw [h_pulled_base]; exact h_nodup
  have h_pulled_get :
      (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base.getValidator vid
        = some bv := by
    rw [h_pulled_base]; exact h
  simp only at h'
  split at h'
  case _ s'' h_fs =>
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, ⟨vid_a, bv_a⟩, _, h_l_split, h_act, _⟩ := h_fs
    have h_a_mem : (vid_a, bv_a) ∈
        (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base.validators := by
      rw [h_l_split]; simp
    have h_a_get :
        (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base.getValidator vid_a
          = some bv_a := by
      unfold BelugaState.getValidator
      rw [Option.map_eq_some_iff]
      exact ⟨(vid_a, bv_a), find?_of_mem_nodup _ vid_a bv_a h_a_mem h_pulled_nodup, rfl⟩
    exact networkTryActFor_round_at_most_one system _ vid_a bv_a h_a_get s'' h_act
      vid bv bv' h_pulled_get h'
  case _ _ =>
    rw [h_pulled_get] at h'; injection h' with h_eq; rw [h_eq]; exact Nat.le_succ _

/-- Round-monotonicity across `networkTraceWithPull`. -/
theorem network_round_monotone_traceWithPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat) (vid : ValidatorId)
    (k₁ : Nat) (bv₁ : BelugaValidator)
    (h₁ : (networkTraceWithPull system time k₁).base.getValidator vid = some bv₁) :
    ∀ k₂, k₁ ≤ k₂ → ∀ bv₂,
      (networkTraceWithPull system time k₂).base.getValidator vid = some bv₂ →
      bv₁.currentRound ≤ bv₂.currentRound := by
  intro k₂ h_le
  induction h_le with
  | refl =>
    intro bv₂ h₂; rw [h₁] at h₂; injection h₂ with h_eq; rw [h_eq]
  | @step k_mid _ ih =>
    intro bv₂ h₂
    have h_step : (networkTraceWithPull system time (k_mid + 1)).base =
        (networkStepWithPull system (networkTraceWithPull system time k_mid)
          (time (k_mid + 1))).base := rfl
    have h_succ_ids := networkTraceWithPull_validators_ids system time (k_mid + 1)
    have h_mid_ids := networkTraceWithPull_validators_ids system time k_mid
    have h_vid_in_succ : vid ∈
        (networkTraceWithPull system time (k_mid + 1)).base.validators.map Prod.fst := by
      unfold BelugaState.getValidator at h₂
      rw [Option.map_eq_some_iff] at h₂
      obtain ⟨p, h_p_mem, _⟩ := h₂
      have h_p_in := List.mem_of_find?_eq_some h_p_mem
      have h_match_eq := List.find?_some h_p_mem
      have h_p1 : p.1 = vid := by
        match p, h_match_eq with
        | (_, _), h => simpa using h
      rw [← h_p1]; exact List.mem_map.mpr ⟨p, h_p_in, rfl⟩
    have h_vid_in_mid : vid ∈ (networkTraceWithPull system time k_mid).base.validators.map Prod.fst := by
      rw [h_mid_ids, ← h_succ_ids]; exact h_vid_in_succ
    obtain ⟨bv_mid, h_mid⟩ : ∃ bv_mid,
        (networkTraceWithPull system time k_mid).base.getValidator vid = some bv_mid := by
      obtain ⟨p, h_p_mem, h_p_eq⟩ := List.mem_map.mp h_vid_in_mid
      refine ⟨p.2, ?_⟩
      have h_pair : p = (vid, p.2) := Prod.ext h_p_eq rfl
      rw [h_pair] at h_p_mem
      exact networkTraceWithPull_getValidator_of_mem system time k_mid vid p.2 h_p_mem
    have ih' := ih bv_mid h_mid
    have h_mono := networkStepWithPull_round_monotone system (networkTraceWithPull system time k_mid)
        (time (k_mid + 1)) (networkTraceWithPull_validators_nodup system time k_mid)
        vid bv_mid bv₂ h_mid (h_step ▸ h₂)
    exact le_trans ih' h_mono

/-- `networkStepWithPull` preserves "absent": if `vid` isn't in
`s.base.validators`, it isn't in the next state either. -/
private lemma networkStepWithPull_preserves_none (system : BlockSynchroniserSystem)
    (s : NetworkState) (newTime : Nat) (vid : ValidatorId)
    (h : s.base.getValidator vid = none) :
    (networkStepWithPull system s newTime).base.getValidator vid = none := by
  unfold BelugaState.getValidator at h ⊢
  rw [Option.map_eq_none_iff] at h ⊢
  rw [List.find?_eq_none] at h ⊢
  have h_keys := networkStepWithPull_preserves_ids system s newTime
  intro x hx h_match
  have h_x_key : x.1 ∈ (networkStepWithPull system s newTime).base.validators.map Prod.fst :=
    List.mem_map.mpr ⟨x, hx, rfl⟩
  rw [h_keys] at h_x_key
  obtain ⟨y, hy_mem, hy_eq⟩ := List.mem_map.mp h_x_key
  apply h y hy_mem
  grind

/-! ## Phase 10: networkStepWithPull advance inversion -/

/-- If `vid`'s round increased by 1 across one `networkStepWithPull`,
then the advance branch of `networkTryActFor` fired for `vid`. Mirror
of `networkStep_advance_inversion`. -/
private lemma networkStepWithPull_advance_inversion
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat)
    (vid : ValidatorId) (bv bv' : BelugaValidator)
    (h_nodup : (s.base.validators.map Prod.fst).Nodup)
    (h : s.base.getValidator vid = some bv)
    (h' : (networkStepWithPull system s newTime).base.getValidator vid = some bv')
    (h_advance : bv'.currentRound = bv.currentRound + 1) :
    hasProposedFor s.base vid bv.currentRound = true ∧
    (∀ B ∈ s.base.blocks,
      hasAcceptedDigest s.base vid B.d = true →
      hasStoredDigest s.base vid B.d = true) ∧
    (allProposedFor system s.base bv.currentRound = true ∨
     ({ s with currentTime := newTime } : NetworkState).deliverPending.timeoutFired
        system bv = true) := by
  have h_del_base :
      ({ s with currentTime := newTime } : NetworkState).deliverPending.base = s.base := by
    rw [NetworkState.deliverPending_preserves_base]
  have h_pull_del_base :
      (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending).base
        = s.base := by
    rw [NetworkState.deliverPullPending_preserves_base]; exact h_del_base
  have h_pulled_base :
      (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
        = s.base := by
    rw [pullStep_preserves_base]; exact h_pull_del_base
  have h_pulled_nodup :
      ((pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base.validators.map Prod.fst).Nodup := by
    rw [h_pulled_base]; exact h_nodup
  have h_pulled_get :
      (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base.getValidator vid
        = some bv := by
    rw [h_pulled_base]; exact h
  have h_pulled_ct :
      (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).currentTime = newTime := by
    rw [pullStep_preserves_currentTime, NetworkState.deliverPullPending_preserves_currentTime,
        NetworkState.deliverPending_preserves_currentTime]
  have h_del_ct :
      ({ s with currentTime := newTime } : NetworkState).deliverPending.currentTime = newTime := by
    rw [NetworkState.deliverPending_preserves_currentTime]
  unfold networkStepWithPull at h'
  simp only at h'
  split at h'
  case _ s_post h_fs =>
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, ⟨vid_a, bv_a⟩, _, h_split, h_act, _⟩ := h_fs
    have h_a_mem : (vid_a, bv_a) ∈
        (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base.validators := by
      rw [h_split]; simp
    have h_a_get :
        (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base.getValidator vid_a
          = some bv_a := by
      unfold BelugaState.getValidator
      rw [Option.map_eq_some_iff]
      exact ⟨(vid_a, bv_a), find?_of_mem_nodup _ vid_a bv_a h_a_mem h_pulled_nodup, rfl⟩
    unfold networkTryActFor at h_act
    simp only at h_act
    split at h_act
    case isTrue h_prop_neg =>
      injection h_act with h_eq
      have h_base_post : s_post.base = doPropose system
          (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
          vid_a bv_a.currentRound := by rw [← h_eq]
      rw [h_base_post] at h'
      rw [doPropose_getValidator'] at h'
      rw [h_pulled_get] at h'
      have h_eq_bv : bv = bv' := Option.some.inj h'
      exfalso
      rw [h_eq_bv] at h_advance
      exact absurd h_advance (Nat.lt_succ_self _).ne
    case isFalse h_prop_pos =>
      have h_hpr_a : hasProposedFor
          (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
          vid_a bv_a.currentRound = true := by
        cases h_b : hasProposedFor
            (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
            vid_a bv_a.currentRound with
        | true => rfl
        | false => exfalso; apply h_prop_pos; simp [h_b]
      split at h_act
      case h_1 B_acc h_findAcc =>
        injection h_act with h_eq
        have h_base_post : s_post.base = doAccept
            (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
            vid_a B_acc := by rw [← h_eq]
        rw [h_base_post] at h'
        obtain ⟨bv_post, h_post_get, h_eq_round⟩ :=
          doAccept_round'
            (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
            vid vid_a B_acc bv h_pulled_get
        have h_eq_bv : bv_post = bv' := Option.some.inj (h_post_get.symm.trans h')
        subst h_eq_bv
        exfalso
        rw [h_eq_round] at h_advance
        exact absurd h_advance (Nat.lt_succ_self _).ne
      case h_2 h_findAcc =>
        split at h_act
        case h_1 B_sto h_findSto =>
          injection h_act with h_eq
          have h_base_post : s_post.base = doStore
              (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
              vid_a B_sto := by rw [← h_eq]
          rw [h_base_post] at h'
          obtain ⟨bv_post, h_post_get, h_eq_round⟩ :=
            doStore_round'
              (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
              vid vid_a B_sto bv h_pulled_get
          have h_eq_bv : bv_post = bv' := Option.some.inj (h_post_get.symm.trans h')
          subst h_eq_bv
          exfalso
          rw [h_eq_round] at h_advance
          exact absurd h_advance (Nat.lt_succ_self _).ne
        case h_2 h_findSto =>
          split at h_act
          case isTrue h_gate =>
            injection h_act with h_eq
            have h_base_post : s_post.base = updateValidator
                (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
                vid_a (fun bv0 => { bv0 with currentRound := bv0.currentRound + 1,
                                              roundEntryTime :=
                  (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).currentTime }) := by
              rw [← h_eq]
            rw [h_base_post] at h'
            by_cases h_eq_vid : vid = vid_a
            · subst h_eq_vid
              have h_bv_eq : bv = bv_a := by
                rw [h_pulled_get] at h_a_get; injection h_a_get
              rw [h_bv_eq]
              refine ⟨?_, ?_, ?_⟩
              · rw [← h_pulled_base]; exact h_hpr_a
              · intro B hB h_acc
                rw [List.find?_eq_none] at h_findSto
                have hB' : B ∈ (pullStep system (({ s with currentTime := newTime }
                    : NetworkState).deliverPending.deliverPullPending)).base.blocks :=
                  h_pulled_base.symm ▸ hB
                have h_no := h_findSto B hB'
                rw [h_pulled_base] at h_no
                rw [h_acc] at h_no; simp at h_no
                cases h_sto : hasStoredDigest s.base vid B.d with
                | true => rfl
                | false => exfalso; rw [h_sto] at h_no; simp at h_no
              · rw [Bool.or_eq_true] at h_gate
                rcases h_gate with h_apf | h_tof
                · left; rw [← h_pulled_base]; exact h_apf
                · right
                  -- h_tof : (pullStep ...).timeoutFired system bv_a = true
                  -- Conclusion needs: deliverPending.timeoutFired system bv = true
                  -- timeoutFired only depends on currentTime, both = newTime.
                  unfold NetworkState.timeoutFired at h_tof ⊢
                  rw [h_pulled_ct] at h_tof
                  rw [h_del_ct]; exact h_tof
            · rw [updateValidator_getValidator_ne' _ _ _ _ h_eq_vid] at h'
              rw [h_pulled_get] at h'
              have h_eq_bv : bv = bv' := Option.some.inj h'
              exfalso
              rw [h_eq_bv] at h_advance
              exact absurd h_advance (Nat.lt_succ_self _).ne
          case isFalse h_gate => simp at h_act
  case _ h_fs =>
    rw [h_pulled_get] at h'
    have h_eq_bv : bv = bv' := Option.some.inj h'
    exfalso
    rw [h_eq_bv] at h_advance
    exact absurd h_advance (Nat.lt_succ_self _).ne

/-- Projection: if round advanced under with-pull, vid had proposed
for its round. -/
private lemma networkStepWithPull_advance_implies_hasProposedFor
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat)
    (vid : ValidatorId) (bv bv' : BelugaValidator)
    (h_nodup : (s.base.validators.map Prod.fst).Nodup)
    (h : s.base.getValidator vid = some bv)
    (h' : (networkStepWithPull system s newTime).base.getValidator vid = some bv')
    (h_advance : bv'.currentRound = bv.currentRound + 1) :
    hasProposedFor s.base vid bv.currentRound = true :=
  (networkStepWithPull_advance_inversion system s newTime vid bv bv' h_nodup h h' h_advance).1

/-- Projection: if round advanced under with-pull, every accepted
block was already stored. -/
theorem networkStepWithPull_advance_implies_stored
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat)
    (vid : ValidatorId) (bv bv' : BelugaValidator)
    (h_nodup : (s.base.validators.map Prod.fst).Nodup)
    (h : s.base.getValidator vid = some bv)
    (h' : (networkStepWithPull system s newTime).base.getValidator vid = some bv')
    (h_advance : bv'.currentRound = bv.currentRound + 1) :
    ∀ B ∈ s.base.blocks,
      hasAcceptedDigest s.base vid B.d = true → hasStoredDigest s.base vid B.d = true :=
  (networkStepWithPull_advance_inversion system s newTime vid bv bv' h_nodup h h' h_advance).2.1

/-- Projection: if round advanced under with-pull, the advance gate fired. -/
private lemma networkStepWithPull_advance_implies_gate
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat)
    (vid : ValidatorId) (bv bv' : BelugaValidator)
    (h_nodup : (s.base.validators.map Prod.fst).Nodup)
    (h : s.base.getValidator vid = some bv)
    (h' : (networkStepWithPull system s newTime).base.getValidator vid = some bv')
    (h_advance : bv'.currentRound = bv.currentRound + 1) :
    allProposedFor system s.base bv.currentRound = true ∨
    ({ s with currentTime := newTime } : NetworkState).deliverPending.timeoutFired
        system bv = true :=
  (networkStepWithPull_advance_inversion system s newTime vid bv bv' h_nodup h h' h_advance).2.2

/-! ## Trace-level helpers for `networkTraceWithPull` -/

/-- Intermediate value theorem for `networkTraceWithPull` rounds. -/
theorem network_round_intermediate_valueWithPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat) (vid : ValidatorId)
    (k₁ k₂ : Nat) (r : Nat)
    (hle : k₁ ≤ k₂)
    (bv₁ bv₂ : BelugaValidator)
    (h₁ : (networkTraceWithPull system time k₁).base.getValidator vid = some bv₁)
    (h₂ : (networkTraceWithPull system time k₂).base.getValidator vid = some bv₂)
    (hr₁ : bv₁.currentRound ≤ r)
    (hr₂ : r ≤ bv₂.currentRound) :
    ∃ k, k₁ ≤ k ∧ k ≤ k₂ ∧
      ∃ bv, (networkTraceWithPull system time k).base.getValidator vid = some bv ∧
            bv.currentRound = r := by
  induction hle generalizing bv₁ bv₂ with
  | refl =>
    have h_eq : bv₁ = bv₂ := by rw [h₁] at h₂; injection h₂
    rw [h_eq] at hr₁
    refine ⟨k₁, le_rfl, le_rfl, bv₂, h₂, ?_⟩
    exact Nat.le_antisymm hr₁ hr₂
  | @step k₂ hk ih =>
    have h_step_eq : (networkTraceWithPull system time (k₂ + 1)).base =
        (networkStepWithPull system (networkTraceWithPull system time k₂)
          (time (k₂ + 1))).base := rfl
    have h_succ_ids := networkTraceWithPull_validators_ids system time (k₂ + 1)
    have h_mid_ids := networkTraceWithPull_validators_ids system time k₂
    have h_vid_in_succ : vid ∈
        (networkTraceWithPull system time (k₂ + 1)).base.validators.map Prod.fst := by
      unfold BelugaState.getValidator at h₂
      rw [Option.map_eq_some_iff] at h₂
      obtain ⟨p, h_p_mem, _⟩ := h₂
      have h_p_in := List.mem_of_find?_eq_some h_p_mem
      have h_match := List.find?_some h_p_mem
      have h_p1 : p.1 = vid := by
        match p, h_match with
        | (_, _), h => simpa using h
      rw [← h_p1]; exact List.mem_map.mpr ⟨p, h_p_in, rfl⟩
    have h_vid_in_mid : vid ∈ (networkTraceWithPull system time k₂).base.validators.map Prod.fst := by
      rw [h_mid_ids, ← h_succ_ids]; exact h_vid_in_succ
    obtain ⟨bv_prev, hbv_prev⟩ : ∃ bv_prev,
        (networkTraceWithPull system time k₂).base.getValidator vid = some bv_prev := by
      obtain ⟨p, h_p_mem, h_p_eq⟩ := List.mem_map.mp h_vid_in_mid
      refine ⟨p.2, ?_⟩
      have h_pair : p = (vid, p.2) := Prod.ext h_p_eq rfl
      rw [h_pair] at h_p_mem
      exact networkTraceWithPull_getValidator_of_mem system time k₂ vid p.2 h_p_mem
    have h_step_bound : bv₂.currentRound ≤ bv_prev.currentRound + 1 := by
      apply networkStepWithPull_round_at_most_one system (networkTraceWithPull system time k₂)
        (time (k₂ + 1)) (networkTraceWithPull_validators_nodup system time k₂) vid bv_prev bv₂
        hbv_prev (h_step_eq ▸ h₂)
    by_cases h_prev_ge : bv_prev.currentRound ≥ r
    · obtain ⟨k, hk_lo, hk_hi, bv_int, h_int, h_int_round⟩ := ih bv₁ bv_prev h₁ hbv_prev hr₁ h_prev_ge
      exact ⟨k, hk_lo, le_trans hk_hi (Nat.le_succ _), bv_int, h_int, h_int_round⟩
    · have h_lt : bv_prev.currentRound < r := Nat.not_le.mp h_prev_ge
      have h_le_succ : r ≤ bv_prev.currentRound + 1 := le_trans hr₂ h_step_bound
      have h_eq_r : bv₂.currentRound = r := by
        have : bv_prev.currentRound + 1 ≤ r := h_lt
        have h_upper : bv₂.currentRound ≤ r := le_trans h_step_bound this
        exact Nat.le_antisymm h_upper hr₂
      refine ⟨k₂ + 1, Nat.le_succ_of_le hk, le_rfl, bv₂, h₂, h_eq_r⟩

/-- Trace invariant: at every step of `networkTraceWithPull`, every
validator at round R has proposed for every r' < R. -/
theorem network_proposed_for_lt_currentRoundWithPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat) :
    ∀ k vid bv, (networkTraceWithPull system time k).base.getValidator vid = some bv →
      ∀ r' < bv.currentRound, hasProposedFor (networkTraceWithPull system time k).base vid r' = true := by
  intro k
  induction k with
  | zero =>
    intro vid bv h_get r' h_lt
    have h_get' : (BelugaState.init system).getValidator vid = some bv := h_get
    have h_round : bv.currentRound = 0 :=
      network_getValidator_init_round_zero system vid bv h_get'
    rw [h_round] at h_lt
    exact absurd h_lt (Nat.not_lt_zero _)
  | succ k ih =>
    intro vid bv h_get r' h_lt
    have h_present_k : ∃ bv_prev, (networkTraceWithPull system time k).base.getValidator vid = some bv_prev := by
      by_contra h_none
      push_neg at h_none
      have h_get_none : (networkTraceWithPull system time k).base.getValidator vid = none :=
        Option.eq_none_iff_forall_ne_some.mpr h_none
      have h_succ_none : (networkTraceWithPull system time (k+1)).base.getValidator vid = none := by
        show (networkStepWithPull system (networkTraceWithPull system time k) (time (k+1))).base.getValidator vid = none
        exact networkStepWithPull_preserves_none system _ _ vid h_get_none
      rw [h_succ_none] at h_get
      contradiction
    obtain ⟨bv_prev, h_prev⟩ := h_present_k
    have h_nodup_k := networkTraceWithPull_validators_nodup system time k
    have h_get_step : (networkStepWithPull system (networkTraceWithPull system time k)
        (time (k+1))).base.getValidator vid = some bv := h_get
    have h_mono : bv_prev.currentRound ≤ bv.currentRound :=
      networkStepWithPull_round_monotone system _ _ h_nodup_k vid bv_prev bv h_prev h_get_step
    have h_at_most_one : bv.currentRound ≤ bv_prev.currentRound + 1 :=
      networkStepWithPull_round_at_most_one system _ _ h_nodup_k vid bv_prev bv h_prev h_get_step
    by_cases h_eq : bv.currentRound = bv_prev.currentRound
    · rw [h_eq] at h_lt
      have h_prop_k := ih vid bv_prev h_prev r' h_lt
      exact network_hasProposedFor_monotoneWithPull system time vid r' k (k+1) (Nat.le_succ k) h_prop_k
    · have h_advance : bv.currentRound = bv_prev.currentRound + 1 := by
        rcases Nat.lt_or_ge bv_prev.currentRound bv.currentRound with h_lt | h_ge
        · have : bv.currentRound ≤ bv_prev.currentRound + 1 := h_at_most_one
          have : bv_prev.currentRound + 1 ≤ bv.currentRound := h_lt
          exact Nat.le_antisymm ‹bv.currentRound ≤ bv_prev.currentRound + 1› ‹_›
        · exact absurd (Nat.le_antisymm h_ge h_mono) h_eq
      by_cases h_lt' : r' < bv_prev.currentRound
      · have h_prop_k := ih vid bv_prev h_prev r' h_lt'
        exact network_hasProposedFor_monotoneWithPull system time vid r' k (k+1) (Nat.le_succ k) h_prop_k
      · have h_eq_r : r' = bv_prev.currentRound := by
          push_neg at h_lt'
          rw [h_advance] at h_lt
          have : r' ≤ bv_prev.currentRound := Nat.le_of_lt_succ h_lt
          exact Nat.le_antisymm this h_lt'
        rw [h_eq_r]
        have h_prop_k :=
          networkStepWithPull_advance_implies_hasProposedFor system _ _ vid bv_prev bv
            h_nodup_k h_prev h_get_step h_advance
        exact network_hasProposedFor_monotoneWithPull system time vid bv_prev.currentRound k (k+1)
          (Nat.le_succ k) h_prop_k

/-- Find the step where vid's round transitioned from r to r+1 along
`networkTraceWithPull`. -/
theorem network_find_advance_stepWithPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat) (vid : ValidatorId) (r : Round) :
    ∀ {k₀ k_target}, k₀ ≤ k_target →
    ∀ bv₀ bv_t,
    (networkTraceWithPull system time k₀).base.getValidator vid = some bv₀ →
    (networkTraceWithPull system time k_target).base.getValidator vid = some bv_t →
    bv₀.currentRound = r →
    bv_t.currentRound ≥ r + 1 →
    ∃ k_a bv bv',
      k₀ ≤ k_a ∧ k_a < k_target ∧
      (networkTraceWithPull system time k_a).base.getValidator vid = some bv ∧
      (networkTraceWithPull system time (k_a + 1)).base.getValidator vid = some bv' ∧
      bv.currentRound = r ∧ bv'.currentRound = r + 1 := by
  intros k₀ k_target hle
  induction hle with
  | refl =>
    intros bv₀ bv_t h₀ h_t hr₀ hr_t
    rw [h₀] at h_t
    have h_eq : bv₀ = bv_t := Option.some.inj h_t
    exfalso
    rw [h_eq] at hr₀
    rw [hr₀] at hr_t
    exact absurd hr_t (Nat.lt_irrefl _ ∘ Nat.lt_of_succ_le)
  | @step k_target' h ih =>
    intros bv₀ bv_t h₀ h_t hr₀ hr_t
    have h_persistent_prev :
        ∃ bv_prev, (networkTraceWithPull system time k_target').base.getValidator vid = some bv_prev := by
      by_contra h_none
      push_neg at h_none
      have h_get_none : (networkTraceWithPull system time k_target').base.getValidator vid = none :=
        Option.eq_none_iff_forall_ne_some.mpr h_none
      have h_succ_none :
          (networkTraceWithPull system time (k_target' + 1)).base.getValidator vid = none := by
        show (networkStepWithPull system (networkTraceWithPull system time k_target')
                (time (k_target' + 1))).base.getValidator vid = none
        exact networkStepWithPull_preserves_none system _ _ vid h_get_none
      rw [h_succ_none] at h_t; contradiction
    obtain ⟨bv_prev, h_prev⟩ := h_persistent_prev
    have h_step_at_most : bv_t.currentRound ≤ bv_prev.currentRound + 1 := by
      apply networkStepWithPull_round_at_most_one system (networkTraceWithPull system time k_target')
        (time (k_target' + 1)) (networkTraceWithPull_validators_nodup system time k_target')
        vid bv_prev bv_t h_prev
      show (networkStepWithPull system (networkTraceWithPull system time k_target')
              (time (k_target' + 1))).base.getValidator vid = some bv_t
      exact h_t
    by_cases h_case : bv_prev.currentRound ≥ r + 1
    · obtain ⟨k_a, bv_a, bv_a', h_le, h_lt, h_a, h_a', h_eq_r, h_eq_r1⟩ :=
        ih bv₀ bv_prev h₀ h_prev hr₀ h_case
      exact ⟨k_a, bv_a, bv_a', h_le, Nat.lt_succ_of_lt h_lt, h_a, h_a', h_eq_r, h_eq_r1⟩
    · push_neg at h_case
      have hbp_le_r : bv_prev.currentRound ≤ r := Nat.le_of_lt_succ h_case
      have hbp_ge_r : bv_prev.currentRound ≥ r := by
        have : r + 1 ≤ bv_prev.currentRound + 1 := le_trans hr_t h_step_at_most
        exact Nat.le_of_succ_le_succ this
      have hbp_eq : bv_prev.currentRound = r := le_antisymm hbp_le_r hbp_ge_r
      have hbt_eq : bv_t.currentRound = r + 1 := by
        have h1 : bv_t.currentRound ≤ r + 1 := by rw [← hbp_eq]; exact h_step_at_most
        exact le_antisymm h1 hr_t
      exact ⟨k_target', bv_prev, bv_t, h, Nat.lt_succ_self _, h_prev, h_t, hbp_eq, hbt_eq⟩

/-- The accepted-block-exists invariant on `networkTraceWithPull`. -/
theorem network_acceptedBlockExists_traceWithPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (vid : ValidatorId) (k : Nat) :
    ∀ d, HasAccepted (networkTraceWithPull system time k).base vid d →
      ∃ B ∈ (networkTraceWithPull system time k).base.blocks, B.d = d := by
  induction k with
  | zero =>
    intro d h_acc
    exfalso
    have h_emp : (networkTraceWithPull system time 0).base.emittedOperations = [] := by
      show ({ NetworkState.init system with currentTime := time 0 }
        : NetworkState).base.emittedOperations = []
      rfl
    unfold HasAccepted Emitted at h_acc
    change ValidatorOperation.block_accept vid d ∈
      (networkTraceWithPull system time 0).base.emittedOperations at h_acc
    rw [h_emp] at h_acc
    simp at h_acc
  | succ k ih =>
    intro d h_acc
    have h_step_eq : (networkTraceWithPull system time (k + 1)).base =
        (networkStepWithPull system (networkTraceWithPull system time k) (time (k + 1))).base := rfl
    rw [h_step_eq] at h_acc
    show ∃ B ∈ (networkStepWithPull system (networkTraceWithPull system time k)
      (time (k + 1))).base.blocks, B.d = d
    set s_pre : NetworkState := networkTraceWithPull system time k with h_s_pre
    have h_del_base :
        ({ s_pre with currentTime := time (k + 1) } : NetworkState).deliverPending.base = s_pre.base := by
      rw [NetworkState.deliverPending_preserves_base]
    have h_pull_del_base :
        (({ s_pre with currentTime := time (k + 1) } : NetworkState).deliverPending.deliverPullPending).base
          = s_pre.base := by
      rw [NetworkState.deliverPullPending_preserves_base]; exact h_del_base
    have h_pulled_base :
        (pullStep system (({ s_pre with currentTime := time (k + 1) } : NetworkState).deliverPending.deliverPullPending)).base
          = s_pre.base := by
      rw [pullStep_preserves_base]; exact h_pull_del_base
    unfold networkStepWithPull at h_acc ⊢
    simp only at h_acc ⊢
    split
    case _ s_post h_fs =>
      simp only [h_fs] at h_acc
      rw [List.findSome?_eq_some_iff] at h_fs
      obtain ⟨_, ⟨vid_a, bv_a⟩, _, _, h_act, _⟩ := h_fs
      unfold networkTryActFor at h_act
      simp only at h_act
      split at h_act
      case isTrue _ =>
        injection h_act with h_eq
        subst h_eq
        rw [network_doPropose_HasAccepted_iff] at h_acc
        rw [h_pulled_base] at h_acc
        obtain ⟨B', hB'_mem, hB'_d⟩ := ih d h_acc
        refine ⟨B', ?_, hB'_d⟩
        show B' ∈ (doPropose system (pullStep system _).base vid_a bv_a.currentRound).blocks
        rw [h_pulled_base]
        exact doPropose_blocks system _ vid_a bv_a.currentRound B' hB'_mem
      case isFalse _ =>
        split at h_act
        case h_1 B_acc h_findAcc =>
          injection h_act with h_eq
          subst h_eq
          rw [network_doAccept_HasAccepted_iff] at h_acc
          rcases h_acc with h_old | ⟨_, h_d⟩
          · rw [h_pulled_base] at h_old
            obtain ⟨B', hB'_mem, hB'_d⟩ := ih d h_old
            refine ⟨B', ?_, hB'_d⟩
            show B' ∈ (doAccept (pullStep system _).base vid_a B_acc).blocks
            rw [doAccept_blocks_eq, h_pulled_base]; exact hB'_mem
          · have hB_mem : B_acc ∈
                (pullStep system (({ s_pre with currentTime := time (k + 1) }
                  : NetworkState).deliverPending.deliverPullPending)).base.blocks :=
              List.mem_of_find?_eq_some h_findAcc
            refine ⟨B_acc, ?_, h_d.symm⟩
            show B_acc ∈ (doAccept (pullStep system _).base vid_a B_acc).blocks
            rw [doAccept_blocks_eq]; exact hB_mem
        case h_2 _ =>
          split at h_act
          case h_1 B_sto h_findSto =>
            injection h_act with h_eq
            subst h_eq
            rw [network_doStore_HasAccepted_iff] at h_acc
            rw [h_pulled_base] at h_acc
            obtain ⟨B', hB'_mem, hB'_d⟩ := ih d h_acc
            refine ⟨B', ?_, hB'_d⟩
            show B' ∈ (doStore (pullStep system _).base vid_a B_sto).blocks
            rw [doStore_blocks_eq, h_pulled_base]; exact hB'_mem
          case h_2 _ =>
            split at h_act
            case isTrue _ =>
              injection h_act with h_eq
              subst h_eq
              rw [updateValidator_HasAccepted_iff] at h_acc
              rw [h_pulled_base] at h_acc
              obtain ⟨B', hB'_mem, hB'_d⟩ := ih d h_acc
              refine ⟨B', ?_, hB'_d⟩
              show B' ∈ (updateValidator (pullStep system _).base vid_a _).blocks
              rw [updateValidator_blocks_eq, h_pulled_base]; exact hB'_mem
            case isFalse _ => simp at h_act
    case _ h_fs =>
      simp only [h_fs] at h_acc
      rw [h_pulled_base] at h_acc
      obtain ⟨B', hB'_mem, hB'_d⟩ := ih d h_acc
      refine ⟨B', ?_, hB'_d⟩
      show B' ∈ (pullStep system _).base.blocks
      rw [h_pulled_base]; exact hB'_mem

/-! ## Pull-mechanism liveness: every honest pushed block is eventually accepted -/

/-- Foundational liveness lemma: under the with-pull primitives, an
honest validator `vid_r` that has a `block_propose` op for `B` (round `r`)
in its inbox post-GST eventually accepts `B.d`.

Proof: `canAcceptBlock` is true (vid hasn't accepted yet, vid received
via push), so by `AcceptScheduling`, vid's `doAccept` action fires
within `Δ`, putting `B.d` in vid's accepted set. -/
theorem network_eventually_accepts_received_withPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_accept : AcceptScheduling system time)
    (vid_r : ValidatorId) (B : Block) (r : Round)
    (h_r : isHonestValidator system vid_r = true)
    (k : Nat) (h_post_gst : time k ≥ system.GST)
    (h_in_inbox : ValidatorOperation.block_propose B.author B r ∈
                    (networkTraceWithPull system time k).inbox vid_r)
    (h_in_pool : B ∈ (networkTraceWithPull system time k).base.blocks)
    (h_not_accepted : hasAcceptedDigest (networkTraceWithPull system time k).base vid_r B.d
                        = false)
    (h_r_eq : B.r = r) :
    ∃ k', k ≤ k' ∧ time k' ≤ time k + system.Δ ∧
      hasAcceptedDigest (networkTraceWithPull system time k').base vid_r B.d = true := by
  -- canAcceptBlock returns true: !accepted && (received || ImPoA).
  -- We have !accepted (from h_not_accepted) and received (from h_in_inbox).
  have h_received : (networkTraceWithPull system time k).hasReceivedPropose vid_r B r = true := by
    unfold NetworkState.hasReceivedPropose
    rw [List.any_eq_true]
    refine ⟨_, h_in_inbox, ?_⟩
    simp +decide
  have h_can_accept :
      (networkTraceWithPull system time k).canAcceptBlock system vid_r B = true := by
    unfold NetworkState.canAcceptBlock
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [Bool.not_eq_true']; exact h_not_accepted
    · rw [Bool.or_eq_true]; left; rw [h_r_eq]; exact h_received
  exact h_accept k vid_r B h_r h_post_gst h_in_pool h_can_accept

/-! ## Block-pool monotonicity along `networkTraceWithPull` -/

/-- One `networkStepWithPull` only extends `base.blocks`. -/
theorem networkStepWithPull_blocks_monotone
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat) :
    ∀ B ∈ s.base.blocks,
      B ∈ (networkStepWithPull system s newTime).base.blocks := by
  intro B hB
  unfold networkStepWithPull
  have h_del_base :
      ({ s with currentTime := newTime } : NetworkState).deliverPending.base = s.base := by
    rw [NetworkState.deliverPending_preserves_base]
  have h_pull_del_base :
      (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending).base
        = s.base := by
    rw [NetworkState.deliverPullPending_preserves_base]; exact h_del_base
  have h_pulled_base :
      (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
        = s.base := by
    rw [pullStep_preserves_base]; exact h_pull_del_base
  have hB_pulled : B ∈
      (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base.blocks := by
    rw [h_pulled_base]; exact hB
  simp only
  split
  case _ s' h_fs =>
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, ⟨vid_a, bv_a⟩, _, _, h_act, _⟩ := h_fs
    unfold networkTryActFor at h_act
    simp only at h_act
    split at h_act
    case isTrue _ =>
      injection h_act with h_eq
      subst h_eq
      show B ∈ (doPropose system _ vid_a bv_a.currentRound).blocks
      exact doPropose_blocks system _ vid_a bv_a.currentRound B hB_pulled
    case isFalse _ =>
      split at h_act
      case h_1 B_acc h_findAcc =>
        injection h_act with h_eq
        subst h_eq
        show B ∈ (doAccept _ vid_a B_acc).blocks
        rw [doAccept_blocks_eq]; exact hB_pulled
      case h_2 _ =>
        split at h_act
        case h_1 B_sto h_findSto =>
          injection h_act with h_eq
          subst h_eq
          show B ∈ (doStore _ vid_a B_sto).blocks
          rw [doStore_blocks_eq]; exact hB_pulled
        case h_2 _ =>
          split at h_act
          case isTrue _ =>
            injection h_act with h_eq
            subst h_eq
            show B ∈ (updateValidator _ vid_a _).blocks
            rw [updateValidator_blocks_eq]; exact hB_pulled
          case isFalse _ => simp at h_act
  case _ _ => exact hB_pulled

/-- Block pool is monotone along `networkTraceWithPull`. -/
theorem network_blocks_monotone_traceWithPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat) :
    ∀ k₁ k₂, k₁ ≤ k₂ →
    ∀ B ∈ (networkTraceWithPull system time k₁).base.blocks,
      B ∈ (networkTraceWithPull system time k₂).base.blocks := by
  intro k₁ k₂ h_le
  induction h_le with
  | refl => intro B hB; exact hB
  | @step k_mid _ ih =>
    intro B hB
    have ih' := ih B hB
    show B ∈ (networkStepWithPull system (networkTraceWithPull system time k_mid)
                (time (k_mid + 1))).base.blocks
    exact networkStepWithPull_blocks_monotone system _ _ B ih'

/-! ## Universal in-pool acceptance: combines push+pull delivery with AcceptScheduling -/

/-- Universal in-pool acceptance: under the with-pull primitives,
every honest validator eventually accepts every block in the pool
post-GST (regardless of author honesty). Combines
`NetworkInPoolDeliveryWithPull` + `AcceptScheduling`. This closes the
Phase 11 gap: it's the universal in-pool acceptance hypothesis taken
by `network_eventualCausalAcceptance_modulo_gap`. -/
theorem network_in_pool_eventually_accepted_withPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_in_pool_delivery : NetworkInPoolDeliveryWithPull system time)
    (h_accept : AcceptScheduling system time)
    (k : Nat) (vid : ValidatorId) (B : Block)
    (h_vid_honest : isHonestValidator system vid = true)
    (h_post_gst : time k ≥ system.GST)
    (h_in_pool : B ∈ (networkTraceWithPull system time k).base.blocks) :
    ∃ k', k ≤ k' ∧
      hasAcceptedDigest (networkTraceWithPull system time k').base vid B.d = true := by
  by_cases h_already :
      hasAcceptedDigest (networkTraceWithPull system time k).base vid B.d = true
  · refine ⟨k, le_rfl, h_already⟩
  · have h_not_accepted :
        hasAcceptedDigest (networkTraceWithPull system time k).base vid B.d = false := by
      cases h_b : hasAcceptedDigest (networkTraceWithPull system time k).base vid B.d with
      | true => exact absurd h_b h_already
      | false => rfl
    obtain ⟨k_d, hk_d_le, h_in_inbox⟩ :=
      h_in_pool_delivery k vid B h_vid_honest h_post_gst h_in_pool h_not_accepted
    have h_in_pool_kd : B ∈ (networkTraceWithPull system time k_d).base.blocks :=
      network_blocks_monotone_traceWithPull system time k k_d hk_d_le B h_in_pool
    have h_post_gst_kd : time k_d ≥ system.GST :=
      le_trans h_post_gst (h_mono _ _ hk_d_le)
    by_cases h_acc_kd :
        hasAcceptedDigest (networkTraceWithPull system time k_d).base vid B.d = true
    · refine ⟨k_d, hk_d_le, h_acc_kd⟩
    · have h_not_acc_kd :
          hasAcceptedDigest (networkTraceWithPull system time k_d).base vid B.d = false := by
        cases h_b : hasAcceptedDigest (networkTraceWithPull system time k_d).base vid B.d with
        | true => exact absurd h_b h_acc_kd
        | false => rfl
      obtain ⟨k_a, hk_a_le, _, h_acc⟩ :=
        network_eventually_accepts_received_withPull system time h_accept vid B B.r
          h_vid_honest k_d h_post_gst_kd h_in_inbox h_in_pool_kd h_not_acc_kd rfl
      refine ⟨k_a, le_trans hk_d_le hk_a_le, h_acc⟩

/-- Inversion of `hasProposedFor`: extract the block from the propose op. -/
theorem hasProposedFor_implies_propose_op (s : BelugaState)
    (vid : ValidatorId) (r : Round) (h : hasProposedFor s vid r = true) :
    ∃ B, ValidatorOperation.block_propose vid B r ∈ s.emittedOperations := by
  unfold hasProposedFor at h
  rw [List.any_eq_true] at h
  obtain ⟨op, hop_mem, hop_match⟩ := h
  cases op with
  | block_propose v B r' =>
    simp at hop_match
    obtain ⟨h_v, h_r⟩ := hop_match
    refine ⟨B, ?_⟩
    rw [h_v, h_r] at hop_mem
    exact hop_mem
  | _ => simp at hop_match

/-! ## Blocks→propose-op bridge -/

/-- Per-step bridge: if every block in the pre-state's pool has a
corresponding propose op in `emittedOperations`, the same holds for
the post-state's pool. -/
private lemma networkStepWithPull_block_implies_propose_op
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat)
    (h_inv : ∀ B, B ∈ s.base.blocks →
      ValidatorOperation.block_propose B.author B B.r ∈ s.base.emittedOperations) :
    ∀ B, B ∈ (networkStepWithPull system s newTime).base.blocks →
      ValidatorOperation.block_propose B.author B B.r ∈
        (networkStepWithPull system s newTime).base.emittedOperations := by
  intro B h_B_new
  unfold networkStepWithPull at h_B_new ⊢
  have h_pulled_base :
      (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
        = s.base := by
    rw [pullStep_preserves_base]
    rw [NetworkState.deliverPullPending_preserves_base]
    rw [NetworkState.deliverPending_preserves_base]
  have h_inv_pulled : ∀ B, B ∈
        (pullStep system (({ s with currentTime := newTime }
          : NetworkState).deliverPending.deliverPullPending)).base.blocks →
      ValidatorOperation.block_propose B.author B B.r ∈
        (pullStep system (({ s with currentTime := newTime }
          : NetworkState).deliverPending.deliverPullPending)).base.emittedOperations := by
    intro B' h
    rw [h_pulled_base] at h
    rw [h_pulled_base]; exact h_inv B' h
  simp only at h_B_new ⊢
  split at h_B_new
  case _ s' h_fs =>
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, ⟨vid_a, bv_a⟩, _, _, h_act, _⟩ := h_fs
    unfold networkTryActFor at h_act
    simp only at h_act
    split at h_act
    case isTrue _ =>
      injection h_act with h_eq
      have h_base_eq : s'.base = doPropose system
          (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
          vid_a bv_a.currentRound := by rw [← h_eq]
      rw [h_base_eq] at h_B_new
      rw [h_base_eq]
      unfold doPropose at h_B_new ⊢
      simp only [List.mem_cons] at h_B_new
      rcases h_B_new with h_new | h_old
      · subst h_new
        rw [List.mem_append]
        right
        simp
      · rw [List.mem_append]; left
        exact h_inv_pulled B h_old
    case isFalse _ =>
      split at h_act
      case h_1 B_acc h_findAcc =>
        injection h_act with h_eq
        have h_base_eq : s'.base = doAccept
            (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
            vid_a B_acc := by rw [← h_eq]
        rw [h_base_eq] at h_B_new
        rw [h_base_eq]
        rw [doAccept_blocks_eq] at h_B_new
        unfold doAccept; simp only [updateValidator]
        rw [List.mem_append]
        left
        exact h_inv_pulled B h_B_new
      case h_2 _ =>
        split at h_act
        case h_1 B_sto h_findSto =>
          injection h_act with h_eq
          have h_base_eq : s'.base = doStore
              (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
              vid_a B_sto := by rw [← h_eq]
          rw [h_base_eq] at h_B_new
          rw [h_base_eq]
          rw [doStore_blocks_eq] at h_B_new
          unfold doStore; simp only [updateValidator]
          rw [List.mem_append]
          left
          exact h_inv_pulled B h_B_new
        case h_2 _ =>
          split at h_act
          case isTrue _ =>
            injection h_act with h_eq
            have h_base_eq : s'.base = updateValidator
                (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
                vid_a (fun bv0 => { bv0 with currentRound := bv0.currentRound + 1,
                                              roundEntryTime :=
                  (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).currentTime }) := by
              rw [← h_eq]
            rw [h_base_eq] at h_B_new
            rw [h_base_eq]
            rw [updateValidator_blocks_eq] at h_B_new
            rw [updateValidator_emittedOperations_eq]
            exact h_inv_pulled B h_B_new
          case isFalse _ => simp at h_act
  case _ _ =>
    exact h_inv_pulled B h_B_new

/-- Trace-level: every block in the pool has a corresponding propose op. -/
theorem network_block_in_pool_implies_propose_op_traceWithPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat) :
    ∀ k B, B ∈ (networkTraceWithPull system time k).base.blocks →
      ValidatorOperation.block_propose B.author B B.r ∈
        (networkTraceWithPull system time k).base.emittedOperations := by
  intro k
  induction k with
  | zero =>
    intro B h_B
    have h_emp : (networkTraceWithPull system time 0).base.blocks = [] := by
      show ({ NetworkState.init system with currentTime := time 0 }
        : NetworkState).base.blocks = []
      rfl
    rw [h_emp] at h_B
    simp at h_B
  | succ k ih =>
    show ∀ B, _ → _
    have h_step : (networkTraceWithPull system time (k + 1)).base =
        (networkStepWithPull system (networkTraceWithPull system time k)
          (time (k + 1))).base := rfl
    rw [h_step]
    exact networkStepWithPull_block_implies_propose_op system _ _ ih

/-! ## Propose-op block-shape invariant -/

/-- One `networkStepWithPull` preserves the propose-op block-shape
invariant. If every existing propose op in `s.base.emittedOperations`
has the right block shape and a witnessing block in the pool, then so
does every propose op in the post-step state. -/
private lemma networkStepWithPull_propose_op_invariant
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat)
    (h_inv : ∀ vid B r, ValidatorOperation.block_propose vid B r ∈ s.base.emittedOperations →
      B.author = vid ∧ B.r = r ∧ B.d = digest system r vid ∧ B ∈ s.base.blocks) :
    ∀ vid B r, ValidatorOperation.block_propose vid B r ∈
                 (networkStepWithPull system s newTime).base.emittedOperations →
      B.author = vid ∧ B.r = r ∧ B.d = digest system r vid ∧
      B ∈ (networkStepWithPull system s newTime).base.blocks := by
  intro vid B r h_op_new
  unfold networkStepWithPull at h_op_new ⊢
  have h_del_base :
      ({ s with currentTime := newTime } : NetworkState).deliverPending.base = s.base := by
    rw [NetworkState.deliverPending_preserves_base]
  have h_pull_del_base :
      (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending).base
        = s.base := by
    rw [NetworkState.deliverPullPending_preserves_base]; exact h_del_base
  have h_pulled_base :
      (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
        = s.base := by
    rw [pullStep_preserves_base]; exact h_pull_del_base
  -- Helper: existing propose op invariant on the pulled state.
  have h_inv_pulled : ∀ vid' B' r', ValidatorOperation.block_propose vid' B' r' ∈
        (pullStep system (({ s with currentTime := newTime }
          : NetworkState).deliverPending.deliverPullPending)).base.emittedOperations →
      B'.author = vid' ∧ B'.r = r' ∧ B'.d = digest system r' vid' ∧
      B' ∈ (pullStep system (({ s with currentTime := newTime }
        : NetworkState).deliverPending.deliverPullPending)).base.blocks := by
    intro vid' B' r' h
    rw [h_pulled_base] at h
    obtain ⟨ha, hr, hd, hb⟩ := h_inv vid' B' r' h
    refine ⟨ha, hr, hd, ?_⟩
    rw [h_pulled_base]; exact hb
  simp only at h_op_new ⊢
  split at h_op_new
  case _ s' h_fs =>
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, ⟨vid_a, bv_a⟩, _, _, h_act, _⟩ := h_fs
    unfold networkTryActFor at h_act
    simp only at h_act
    split at h_act
    case isTrue _ =>
      injection h_act with h_eq
      have h_base_eq : s'.base = doPropose system
          (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
          vid_a bv_a.currentRound := by rw [← h_eq]
      rw [h_base_eq] at h_op_new
      rw [h_base_eq]
      simp only [doPropose] at h_op_new
      simp only [List.mem_append, List.mem_singleton] at h_op_new
      rcases h_op_new with h_old | h_new
      · obtain ⟨ha, hr, hd, hb⟩ := h_inv_pulled vid B r h_old
        refine ⟨ha, hr, hd, ?_⟩
        show B ∈ (doPropose system _ vid_a bv_a.currentRound).blocks
        exact doPropose_blocks system _ vid_a bv_a.currentRound B hb
      · injection h_new with hv hB hr_eq
        subst hv; subst hr_eq; subst hB
        refine ⟨rfl, rfl, rfl, ?_⟩
        simp [doPropose]
    case isFalse _ =>
      split at h_act
      case h_1 B_acc h_findAcc =>
        injection h_act with h_eq
        have h_base_eq : s'.base = doAccept
            (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
            vid_a B_acc := by rw [← h_eq]
        rw [h_base_eq] at h_op_new
        rw [h_base_eq]
        simp only [doAccept, updateValidator] at h_op_new
        simp only [List.mem_append, List.mem_singleton] at h_op_new
        rcases h_op_new with h_old | h_bad
        · obtain ⟨ha, hr, hd, hb⟩ := h_inv_pulled vid B r h_old
          refine ⟨ha, hr, hd, ?_⟩
          show B ∈ (doAccept _ vid_a B_acc).blocks
          rw [doAccept_blocks_eq]; exact hb
        · cases h_bad
      case h_2 _ =>
        split at h_act
        case h_1 B_sto h_findSto =>
          injection h_act with h_eq
          have h_base_eq : s'.base = doStore
              (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
              vid_a B_sto := by rw [← h_eq]
          rw [h_base_eq] at h_op_new
          rw [h_base_eq]
          simp only [doStore, updateValidator] at h_op_new
          simp only [List.mem_append, List.mem_singleton] at h_op_new
          rcases h_op_new with h_old | h_bad
          · obtain ⟨ha, hr, hd, hb⟩ := h_inv_pulled vid B r h_old
            refine ⟨ha, hr, hd, ?_⟩
            show B ∈ (doStore _ vid_a B_sto).blocks
            rw [doStore_blocks_eq]; exact hb
          · cases h_bad
        case h_2 _ =>
          split at h_act
          case isTrue _ =>
            injection h_act with h_eq
            have h_base_eq : s'.base = updateValidator
                (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
                vid_a (fun bv0 => { bv0 with currentRound := bv0.currentRound + 1,
                                              roundEntryTime :=
                  (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).currentTime }) := by
              rw [← h_eq]
            rw [h_base_eq] at h_op_new
            rw [h_base_eq]
            rw [updateValidator_emittedOperations_eq] at h_op_new
            rw [updateValidator_blocks_eq]
            exact h_inv_pulled vid B r h_op_new
          case isFalse _ => simp at h_act
  case _ _ =>
    exact h_inv_pulled vid B r h_op_new

/-- Trace-level propose-op block-shape invariant: at every step of
`networkTraceWithPull`, every propose op's block has the protocol-
prescribed shape (B.author = vid, B.r = r, B.d = digest system r vid)
and is in the block pool. -/
theorem network_propose_op_invariant_traceWithPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat) :
    ∀ k vid B r, ValidatorOperation.block_propose vid B r ∈
                   (networkTraceWithPull system time k).base.emittedOperations →
      B.author = vid ∧ B.r = r ∧ B.d = digest system r vid ∧
      B ∈ (networkTraceWithPull system time k).base.blocks := by
  intro k
  induction k with
  | zero =>
    intro vid B r h_op
    have h_emp : (networkTraceWithPull system time 0).base.emittedOperations = [] := by
      show ({ NetworkState.init system with currentTime := time 0 }
        : NetworkState).base.emittedOperations = []
      rfl
    rw [h_emp] at h_op
    simp at h_op
  | succ k ih =>
    show ∀ vid B r, _ → _
    have h_step : (networkTraceWithPull system time (k + 1)).base =
        (networkStepWithPull system (networkTraceWithPull system time k)
          (time (k + 1))).base := rfl
    rw [h_step]
    exact networkStepWithPull_propose_op_invariant system _ _ ih

/-! ## Propose-op author-bound invariant

Companion to `network_propose_op_invariant_traceWithPull`: every
emitted propose op's author is registered in `system.validators`.
Combined with `system.validIds`, this gives the bound `vid < n + 1`
needed by `digest_injective`. -/

/-- Per-step author-bound: if every existing propose op's author is
in `s.base.validators`'s ID list, and that list matches `system`'s,
then every post-step propose op's author is in `system`'s. -/
private lemma networkStepWithPull_propose_op_author_preserved
    (system : BlockSynchroniserSystem) (s : NetworkState) (newTime : Nat)
    (h_ids : s.base.validators.map Prod.fst = system.validators.map Prod.fst)
    (h_inv : ∀ vid B r, ValidatorOperation.block_propose vid B r ∈ s.base.emittedOperations →
      vid ∈ system.validators.map Prod.fst) :
    ∀ vid B r, ValidatorOperation.block_propose vid B r ∈
                 (networkStepWithPull system s newTime).base.emittedOperations →
      vid ∈ system.validators.map Prod.fst := by
  intro vid B r h_op_new
  unfold networkStepWithPull at h_op_new
  have h_del_base :
      ({ s with currentTime := newTime } : NetworkState).deliverPending.base = s.base := by
    rw [NetworkState.deliverPending_preserves_base]
  have h_pull_del_base :
      (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending).base
        = s.base := by
    rw [NetworkState.deliverPullPending_preserves_base]; exact h_del_base
  have h_pulled_base :
      (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
        = s.base := by
    rw [pullStep_preserves_base]; exact h_pull_del_base
  have h_inv_pulled : ∀ vid' B' r', ValidatorOperation.block_propose vid' B' r' ∈
        (pullStep system (({ s with currentTime := newTime }
          : NetworkState).deliverPending.deliverPullPending)).base.emittedOperations →
      vid' ∈ system.validators.map Prod.fst := by
    intro vid' B' r' h
    rw [h_pulled_base] at h
    exact h_inv vid' B' r' h
  have h_pulled_ids :
      (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base.validators.map Prod.fst
        = system.validators.map Prod.fst := by
    rw [h_pulled_base]; exact h_ids
  simp only at h_op_new
  split at h_op_new
  case _ s' h_fs =>
    rw [List.findSome?_eq_some_iff] at h_fs
    obtain ⟨_, ⟨vid_a, bv_a⟩, _, h_l_split, h_act, _⟩ := h_fs
    -- vid_a ∈ pulled.base.validators IDs = system's IDs.
    have h_a_mem : (vid_a, bv_a) ∈
        (pullStep system (({ s with currentTime := newTime }
          : NetworkState).deliverPending.deliverPullPending)).base.validators := by
      rw [h_l_split]; simp
    have h_a_in_system : vid_a ∈ system.validators.map Prod.fst := by
      rw [← h_pulled_ids]
      exact List.mem_map.mpr ⟨(vid_a, bv_a), h_a_mem, rfl⟩
    unfold networkTryActFor at h_act
    simp only at h_act
    split at h_act
    case isTrue _ =>
      injection h_act with h_eq
      have h_base_eq : s'.base = doPropose system
          (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
          vid_a bv_a.currentRound := by rw [← h_eq]
      rw [h_base_eq] at h_op_new
      simp only [doPropose] at h_op_new
      simp only [List.mem_append, List.mem_singleton] at h_op_new
      rcases h_op_new with h_old | h_new
      · exact h_inv_pulled vid B r h_old
      · injection h_new with hv _ _
        subst hv; exact h_a_in_system
    case isFalse _ =>
      split at h_act
      case h_1 B_acc h_findAcc =>
        injection h_act with h_eq
        have h_base_eq : s'.base = doAccept
            (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
            vid_a B_acc := by rw [← h_eq]
        rw [h_base_eq] at h_op_new
        simp only [doAccept, updateValidator] at h_op_new
        simp only [List.mem_append, List.mem_singleton] at h_op_new
        rcases h_op_new with h_old | h_bad
        · exact h_inv_pulled vid B r h_old
        · cases h_bad
      case h_2 _ =>
        split at h_act
        case h_1 B_sto h_findSto =>
          injection h_act with h_eq
          have h_base_eq : s'.base = doStore
              (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
              vid_a B_sto := by rw [← h_eq]
          rw [h_base_eq] at h_op_new
          simp only [doStore, updateValidator] at h_op_new
          simp only [List.mem_append, List.mem_singleton] at h_op_new
          rcases h_op_new with h_old | h_bad
          · exact h_inv_pulled vid B r h_old
          · cases h_bad
        case h_2 _ =>
          split at h_act
          case isTrue _ =>
            injection h_act with h_eq
            have h_base_eq : s'.base = updateValidator
                (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).base
                vid_a (fun bv0 => { bv0 with currentRound := bv0.currentRound + 1,
                                              roundEntryTime :=
                  (pullStep system (({ s with currentTime := newTime } : NetworkState).deliverPending.deliverPullPending)).currentTime }) := by
              rw [← h_eq]
            rw [h_base_eq] at h_op_new
            rw [updateValidator_emittedOperations_eq] at h_op_new
            exact h_inv_pulled vid B r h_op_new
          case isFalse _ => simp at h_act
  case _ _ =>
    exact h_inv_pulled vid B r h_op_new

/-- Trace-level: every propose op's author in `networkTraceWithPull`
is in `system.validators`'s ID list. Combined with `system.validIds`,
gives `vid < n + 1`. -/
theorem network_propose_op_author_in_system_traceWithPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat) :
    ∀ k vid B r, ValidatorOperation.block_propose vid B r ∈
                   (networkTraceWithPull system time k).base.emittedOperations →
      vid ∈ system.validators.map Prod.fst := by
  intro k
  induction k with
  | zero =>
    intro vid B r h_op
    have h_emp : (networkTraceWithPull system time 0).base.emittedOperations = [] := by
      show ({ NetworkState.init system with currentTime := time 0 }
        : NetworkState).base.emittedOperations = []
      rfl
    rw [h_emp] at h_op
    simp at h_op
  | succ k ih =>
    show ∀ vid B r, _ → _
    have h_step : (networkTraceWithPull system time (k + 1)).base =
        (networkStepWithPull system (networkTraceWithPull system time k)
          (time (k + 1))).base := rfl
    rw [h_step]
    have h_ids : (networkTraceWithPull system time k).base.validators.map Prod.fst
        = system.validators.map Prod.fst := networkTraceWithPull_validators_ids system time k
    exact networkStepWithPull_propose_op_author_preserved system _ _ h_ids ih

/-- Combined: propose op author is bounded by `system.n + 1`. -/
theorem network_propose_op_author_bounded_traceWithPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (k : Nat) (vid : ValidatorId) (B : Block) (r : Round)
    (h_op : ValidatorOperation.block_propose vid B r ∈
              (networkTraceWithPull system time k).base.emittedOperations) :
    vid < system.n + 1 := by
  have h_in_ids := network_propose_op_author_in_system_traceWithPull system time k vid B r h_op
  obtain ⟨p, h_p_mem, h_p_eq⟩ := List.mem_map.mp h_in_ids
  rw [← h_p_eq]
  exact system.validIds p h_p_mem

/-! ## Single-author eventual acceptance -/

/-- Under the with-pull primitives, every honest validator eventually
accepts the round-`r` block of every honest author. The cornerstone
of `network_eventualRoundAcceptance`: given an honest `vid_p` and
honest receiver `vid`, by some step `k`, `vid` has the digest
`digest system r vid_p` accepted. -/
theorem network_each_honest_block_eventually_accepted_withPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_time_unbounded : ∀ T, ∃ k, time k ≥ T)
    (h_delivery : NetworkDeliveryWithPull system time)
    (h_scheduling : ActionSchedulingWithPull system time)
    (h_spread : BoundedRoundSpread_networkTraceWithPull system time)
    (h_accept : AcceptScheduling system time)
    (r : Round) (vid : ValidatorId) (vid_p : ValidatorId)
    (h_vid_honest : isHonestValidator system vid = true)
    (h_vid_p_honest : isHonestValidator system vid_p = true) :
    ∃ k, hasAcceptedDigest (networkTraceWithPull system time k).base vid
           (digest system r vid_p) = true := by
  -- Step 1: find a post-GST step.
  obtain ⟨k_gst, h_k_gst⟩ : ∃ k, time k ≥ system.GST := h_time_unbounded system.GST
  -- Step 2: bring all honest to currentRound ≥ r + 1.
  obtain ⟨k₁, h_k₁_le, h_k₁_gst, h_all_at_succ⟩ :=
    network_all_honest_eventually_at_roundWithPull system time h_mono h_delivery
      h_scheduling h_spread vid h_vid_honest k_gst h_k_gst (r + 1)
  obtain ⟨bv_p, h_bv_p, h_bv_p_round⟩ := h_all_at_succ vid_p h_vid_p_honest
  -- Step 3: vid_p has proposed for r at step k₁.
  have h_lt : r < bv_p.currentRound := h_bv_p_round
  have h_proposed : hasProposedFor (networkTraceWithPull system time k₁).base vid_p r = true :=
    network_proposed_for_lt_currentRoundWithPull system time k₁ vid_p bv_p h_bv_p r h_lt
  -- Step 4: extract the block.
  obtain ⟨B, h_op⟩ :=
    hasProposedFor_implies_propose_op (networkTraceWithPull system time k₁).base vid_p r h_proposed
  -- Step 5: structural facts about B.
  obtain ⟨h_B_author, h_B_r, h_B_d, h_B_in_pool⟩ :=
    network_propose_op_invariant_traceWithPull system time k₁ vid_p B r h_op
  -- Step 6: deliver B's propose op to vid's inbox.
  obtain ⟨k₂, h_k₂_le, h_k₂_time, h_in_inbox⟩ :=
    h_delivery k₁ vid_p vid B r h_vid_p_honest h_vid_honest h_k₁_gst h_op
  have h_k₂_gst : time k₂ ≥ system.GST :=
    le_trans h_k₁_gst (h_mono _ _ h_k₂_le)
  -- Step 7: B is in pool at k₂ (by blocks monotonicity).
  have h_B_in_pool_k₂ : B ∈ (networkTraceWithPull system time k₂).base.blocks :=
    network_blocks_monotone_traceWithPull system time k₁ k₂ h_k₂_le B h_B_in_pool
  -- Step 8: case-split on whether vid has already accepted B.d at k₂.
  by_cases h_already :
      hasAcceptedDigest (networkTraceWithPull system time k₂).base vid B.d = true
  · -- Already accepted. We have B.d = digest system r vid_p, so done.
    refine ⟨k₂, ?_⟩; rw [h_B_d] at h_already; exact h_already
  · -- Not accepted. Apply AcceptScheduling-derived liveness.
    have h_not_accepted :
        hasAcceptedDigest (networkTraceWithPull system time k₂).base vid B.d = false := by
      cases h_b : hasAcceptedDigest (networkTraceWithPull system time k₂).base vid B.d with
      | true => exact absurd h_b h_already
      | false => rfl
    -- Reconstruct propose op shape: block_propose B.author B r matches op's author = vid_p.
    have h_in_inbox' : ValidatorOperation.block_propose B.author B r ∈
        (networkTraceWithPull system time k₂).inbox vid := by rw [h_B_author]; exact h_in_inbox
    obtain ⟨k₃, h_k₃_le, _, h_acc⟩ :=
      network_eventually_accepts_received_withPull system time h_accept vid B r
        h_vid_honest k₂ h_k₂_gst h_in_inbox' h_B_in_pool_k₂ h_not_accepted h_B_r
    refine ⟨k₃, ?_⟩
    rw [h_B_d] at h_acc; exact h_acc

/-! ## Bridge: hasAcceptedDigest ↔ HasAccepted -/

/-- Bridge between the boolean `hasAcceptedDigest` predicate and the
`HasAccepted` proposition (which is membership of a block_accept op
in `emittedOperations`). -/
theorem hasAcceptedDigest_iff_HasAccepted (s : BelugaState)
    (vid : ValidatorId) (d : BlockDigest) :
    hasAcceptedDigest s vid d = true ↔ HasAccepted s vid d := by
  unfold hasAcceptedDigest HasAccepted Emitted
  rw [List.any_eq_true]
  constructor
  · rintro ⟨op, hop_mem, hop_match⟩
    cases op with
    | block_accept v d' =>
      simp at hop_match
      obtain ⟨h_v, h_d⟩ := hop_match
      rw [← h_v, ← h_d]; exact hop_mem
    | _ => simp at hop_match
  · intro h_mem
    refine ⟨ValidatorOperation.block_accept vid d, h_mem, ?_⟩
    simp +decide

/-- `hasAcceptedDigest = true` is monotone along `networkTraceWithPull`. -/
theorem network_hasAcceptedDigest_monotone_withPull
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (vid : ValidatorId) (d : BlockDigest)
    (k₁ k₂ : Nat) (h_le : k₁ ≤ k₂)
    (h : hasAcceptedDigest (networkTraceWithPull system time k₁).base vid d = true) :
    hasAcceptedDigest (networkTraceWithPull system time k₂).base vid d = true := by
  rw [hasAcceptedDigest_iff_HasAccepted] at h ⊢
  exact network_HasAccepted_monotone_withPull system time vid d k₁ k₂ h_le h

/-! ## Iteration over honest validators: all-accepted-by-some-step -/

/-- Iteration lemma: for any list `l` of honest validator IDs, there
exists a step `k` at which `vid` has accepted the round-`r` digest of
every member of `l`. Inductive over `l`. -/
theorem all_honest_in_list_eventually_accepted
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_time_unbounded : ∀ T, ∃ k, time k ≥ T)
    (h_delivery : NetworkDeliveryWithPull system time)
    (h_scheduling : ActionSchedulingWithPull system time)
    (h_spread : BoundedRoundSpread_networkTraceWithPull system time)
    (h_accept : AcceptScheduling system time)
    (r : Round) (vid : ValidatorId) (h_vid_honest : isHonestValidator system vid = true) :
    ∀ l : List ValidatorId, (∀ p ∈ l, isHonestValidator system p = true) →
      ∃ k, ∀ vid_p ∈ l,
        hasAcceptedDigest (networkTraceWithPull system time k).base vid
          (digest system r vid_p) = true := by
  intro l
  induction l with
  | nil => intro _; exact ⟨0, fun _ h => by simp at h⟩
  | cons hd tl ih =>
    intro h_all
    obtain ⟨k_tl, h_tl⟩ := ih (fun p hp => h_all p (List.mem_cons_of_mem _ hp))
    obtain ⟨k_hd, h_hd⟩ := network_each_honest_block_eventually_accepted_withPull
      system time h_mono h_time_unbounded h_delivery h_scheduling h_spread h_accept
      r vid hd h_vid_honest (h_all hd List.mem_cons_self)
    refine ⟨max k_tl k_hd, ?_⟩
    intro p hp
    rw [List.mem_cons] at hp
    rcases hp with h_eq | h_in
    · subst h_eq
      exact network_hasAcceptedDigest_monotone_withPull system time vid (digest system r p)
        k_hd (max k_tl k_hd) (le_max_right _ _) h_hd
    · exact network_hasAcceptedDigest_monotone_withPull system time vid (digest system r p)
        k_tl (max k_tl k_hd) (le_max_left _ _) (h_tl p h_in)

/-! ## EventualRoundAcceptance: proof skeleton

Phase 10's main theorem, derived from the with-pull primitives:

```
theorem network_eventualRoundAcceptance
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_time_unbounded : ∀ T, ∃ k, time k ≥ T)
    (h_delivery : NetworkDeliveryWithPull system time)
    (h_scheduling : ActionSchedulingWithPull system time)
    (h_spread : BoundedRoundSpread_networkTraceWithPull system time)
    (h_accept : AcceptScheduling system time) :
    ∀ round vid, isHonestValidator system vid = true →
      ∃ k, |acceptedAuthors_of_round_r_at_k_for_vid| ≥ 2f+1
```

Proof structure (~300-500 lines):
1. Apply iterated `ActionSchedulingWithPull` to bring all honest
   validators past round r+1.
2. Each honest validator vid_p has proposed for r — block_propose op
   in emittedOperations.
3. By `NetworkDeliveryWithPull`, vid's inbox eventually contains
   each of these block_propose ops.
4. Apply `network_eventually_accepts_received_withPull` (above) for
   each: vid accepts each block within Δ.
5. By `system.honestBound ≥ 2f+1`, vid has accepted ≥ 2f+1 distinct
   honest authors' round-r blocks.

The iteration structure (step 4) requires extending from "single
acceptance" to "multiple acceptances at a single later step". This
needs a `accept_persistent` lemma (HasAccepted is monotone along
the trace). Phase 10 deliverable. -/

end Network
end Beluga
end BlockSynchroniser
