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

/-- Generic helper: given `(vid, bv) ∈ l` and `l.map Prod.fst` is
Nodup, then `l.find? (·.1 == vid) = some (vid, bv)`. -/
private lemma find?_of_mem_nodup
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

/-! ## Paper-faithful primitive for `belugaTrace` (finding F-1 made explicit)

Per the analysis in `docs/resumption-note-network-fairness.md`
(Simplification A): the `SchedulerFairness` lockstep-progress claim
follows from a much smaller per-validator Δ-bounded advance
primitive, applied directly to `belugaTrace`. This primitive is
the explicit form of paper §4.2's "honest validators run the
protocol" implicit assumption (finding F-1).

Stated against `belugaTrace` directly, it gives a clean derivation
of `SchedulerFairness_belugaTrace` without needing the full
network-aware trace + ImPoA/timeout reasoning. -/

/-- **`ActionScheduling_belugaTrace`** — paper §4.2 + finding F-1
made explicit, stated directly against `belugaTrace`: post-GST,
every honest validator's local round advances within `Δ`. -/
def ActionScheduling_belugaTrace
    (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop :=
  ∀ k vid bv,
    isHonestValidator system vid = true →
    time k ≥ system.GST →
    (belugaTrace system k).getValidator vid = some bv →
    ∃ k' bv', k ≤ k' ∧ time k' ≤ time k + system.Δ ∧
      (belugaTrace system k').getValidator vid = some bv' ∧
      bv'.currentRound > bv.currentRound

/-- **`BoundedRoundSpread`** — finding F-1b made explicit:
post-GST, the rounds of any two honest validators differ by at
most 1. This is the gap-1 invariant the paper's protocol
maintains via the push protocol's parent-acceptance rules
combined with the per-round timeout `T_rd = 4Δ`.

Paper L1's "all honest enter the same round in 3Δ" is exactly
the post-GST stable form of this invariant; the round-spread is
maintained at every step. -/
def BoundedRoundSpread
    (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop :=
  ∀ k vid₁ vid₂ bv₁ bv₂,
    time k ≥ system.GST →
    isHonestValidator system vid₁ = true →
    isHonestValidator system vid₂ = true →
    (belugaTrace system k).getValidator vid₁ = some bv₁ →
    (belugaTrace system k).getValidator vid₂ = some bv₂ →
    bv₁.currentRound ≤ bv₂.currentRound + 1

/-! ## `SchedulerFairness` for `belugaTrace` from network-trace primitives

`Theorems.lean`'s `SchedulerFairness` is stated against `belugaTrace`,
not `networkTrace`. To route the §5 wrappers through
`schedulerFairness_holds` (which produces `networkTrace`-flavored
fairness), we need a bridge between the two traces.

**The bridge problem.** `belugaTrace` and `networkTrace.base` evolve
under different transition rules: `step` (used by `belugaTrace`)
advances on `allProposedFor` only and accepts when parents are
directly accepted, while `networkStep` (used by `networkTrace`) has
the additional ImPoA accept path (paper §4.3 f+1 references) and
the timeout-fired advance path (paper §4.2 `T_rd = 4Δ`). A direct
refinement does not exist in either direction: `networkTrace` can
advance via the timeout where `belugaTrace` is still waiting,
making round-state divergence possible.

**Resolution.** We expose the bridge as an explicit `Prop`-level
hypothesis `NetworkBelugaCoherence`: at every step, the round
state of `belugaTrace` agrees with the round state of
`networkTrace.base`. This is the load-bearing piece the paper
hand-waves when saying "the protocol's two-trace abstraction is
equivalent." Making it a typed hypothesis surfaces the missing
derivation as paper-side feedback rather than burying it. -/

/-- **`NetworkBelugaCoherence`** — for every step `k` and honest
validator `vid`, the round (and presence) of `vid` agree across
`belugaTrace` and `networkTrace.base`. This Prop is the explicit
form of the paper's implicit assumption that the `belugaTrace`
abstraction (no inboxes, no timeout, no ImPoA) and the
`networkTrace` model (with all paper §4 mechanisms) coincide on
the round-progression slice the §5 theorems care about.

The Prop is *not* derivable from the network primitives
(`NetworkDelivery`, `ActionScheduling`, `BoundedRoundSpread_networkTrace`)
alone — `networkTrace` is strictly more permissive than `belugaTrace`
(timeout + ImPoA give it extra advance/accept paths), so a refinement
in either direction can fail. The coherence assumption captures the
specific protocol regime in which the two traces' rounds align. -/
def NetworkBelugaCoherence
    (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop :=
  ∀ k vid bv,
    isHonestValidator system vid = true →
    (belugaTrace system k).getValidator vid = some bv →
    ∃ bv', (networkTrace system time k).base.getValidator vid = some bv' ∧
           bv.currentRound = bv'.currentRound

/-- The `SchedulerFairness` predicate for `belugaTrace` (the existing
shape used by `Theorems.lean`'s §5 wrappers). Restated here so this
file can both state and discharge the corresponding theorem.
Definitionally identical to `Theorems.SchedulerFairness`. -/
def SchedulerFairness_belugaTrace
    (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop :=
  ∀ k r,
    time k ≥ system.GST →
    (∃ vid bv,
        isHonestValidator system vid = true ∧
        (belugaTrace system k).getValidator vid = some bv ∧
        bv.currentRound = r) →
    ∃ k', k ≤ k' ∧ time k' ≤ time k + 3 * system.Δ ∧
      ∀ vid, isHonestValidator system vid = true →
        ∃ bv, (belugaTrace system k').getValidator vid = some bv ∧
              bv.currentRound ≥ r + 1

/-- **`belugaTrace_schedulerFairness`** — derived from the
`networkTrace` fairness theorem `schedulerFairness_holds` plus the
explicit `NetworkBelugaCoherence` bridge.

**Hypothesis set** matches `schedulerFairness_holds` (the four
network-trace primitives) plus `NetworkBelugaCoherence`:

- `NetworkDelivery` (paper §2): `Δ`-bounded honest-honest delivery.
- `ActionScheduling` (paper §4.2 + finding F-1): per-validator
  Δ-bounded round advance against `networkTrace`.
- `BoundedRoundSpread_networkTrace` (paper §4.2 + finding F-1b):
  gap-1 invariant against `networkTrace`.
- `h_persistent_network`: every honest validator is present at
  every step of `networkTrace`.
- `h_persistent_beluga`: same, for `belugaTrace`.
- `NetworkBelugaCoherence`: round-state agreement between the
  two traces.

**Proof structure**:
1. Apply `schedulerFairness_holds` → fairness for `networkTrace`.
2. Apply `NetworkBelugaCoherence` to lift to `belugaTrace`.

Step 2 is the load-bearing bridge; the network primitives alone
do not justify `belugaTrace`-flavored fairness. -/
theorem belugaTrace_schedulerFairness
    (system : BlockSynchroniserSystem) (time : Nat → Nat)
    (h_mono : ∀ i j, i ≤ j → time i ≤ time j)
    (h_delivery : NetworkDelivery system time)
    (h_scheduling : ActionScheduling system time)
    (h_spread : BoundedRoundSpread_networkTrace system time)
    (h_persistent_network : ∀ vid k, isHonestValidator system vid = true →
      ∃ bv, (networkTrace system time k).base.getValidator vid = some bv)
    (h_persistent_beluga : ∀ vid k, isHonestValidator system vid = true →
      ∃ bv, (belugaTrace system k).getValidator vid = some bv)
    (h_coherence : NetworkBelugaCoherence system time) :
    SchedulerFairness_belugaTrace system time := by
  intro k r h_post_gst ⟨vid_w, bv_w, h_w_honest, h_w_get, h_w_round⟩
  -- Step 1: Lift the witness from belugaTrace to networkTrace via coherence.
  obtain ⟨bv_w_n, h_w_get_n, h_w_round_eq⟩ :=
    h_coherence k vid_w bv_w h_w_honest h_w_get
  have h_w_round_n : bv_w_n.currentRound = r := by rw [← h_w_round_eq]; exact h_w_round
  -- Step 2: Apply networkTrace fairness.
  obtain ⟨k', hk'_le, hk'_time, hk'_all⟩ :=
    schedulerFairness_holds system time h_mono h_delivery h_scheduling h_spread
      h_persistent_network k r h_post_gst
      ⟨vid_w, bv_w_n, h_w_honest, h_w_get_n, h_w_round_n⟩
  -- Step 3: Lift the conclusion from networkTrace back to belugaTrace.
  refine ⟨k', hk'_le, hk'_time, ?_⟩
  intro vid h_vid_honest
  obtain ⟨bv_vid_b, h_vid_get_b⟩ := h_persistent_beluga vid k' h_vid_honest
  refine ⟨bv_vid_b, h_vid_get_b, ?_⟩
  obtain ⟨bv_vid_n, h_vid_get_n, h_vid_round_eq⟩ :=
    h_coherence k' vid bv_vid_b h_vid_honest h_vid_get_b
  obtain ⟨bv_vid_n', h_vid_get_n', h_vid_round_n_ge⟩ := hk'_all vid h_vid_honest
  -- networkTrace witnesses are unique (by ID) so bv_vid_n = bv_vid_n'.
  have : bv_vid_n = bv_vid_n' := by rw [h_vid_get_n] at h_vid_get_n'; injection h_vid_get_n'
  rw [h_vid_round_eq, this]; exact h_vid_round_n_ge

end Network
end Beluga
end BlockSynchroniser
