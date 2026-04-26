/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Wall-clock timing on a `Trace` (paper §2: GST + Δ partial-synchrony).

This module is the structural prerequisite for *timing-flavored* lemmas:
paper §5 Lemmas 1 and 2 (3Δ round-entry / round-latency), Appendix D
liveness lemmas, and Appendix C deterministic latency bounds. Without it,
those lemmas can only be stated abstractly with `∃ k`. With it, they can
quantify over wall-clock time `t ≥ GST + 3Δ` etc.

The model: a `TimeMap` is a map from trace step index `i : ℕ` to a
wall-clock value `time i : ℕ`. Monotone and unbounded so future events
have non-decreasing timestamps and time eventually exceeds every bound.
-/
import BlockSynchroniser.System
import BlockSynchroniser.State
import BlockSynchroniser.Trace

namespace BlockSynchroniser

/-- A wall-clock time map. `time i` is the timestamp of step `i`. -/
abbrev TimeMap := Nat → Nat

namespace TimeMap

/-- Monotone time map: timestamps are non-decreasing in step index. -/
def Monotone (time : TimeMap) : Prop :=
  ∀ i j, i ≤ j → time i ≤ time j

/-- Unbounded time map: every clock value is eventually surpassed. -/
def Unbounded (time : TimeMap) : Prop :=
  ∀ T, ∃ i, time i ≥ T

/-- Combined well-formedness: monotone and unbounded. -/
def WellFormed (time : TimeMap) : Prop :=
  Monotone time ∧ Unbounded time

/-- The trivial *step-equals-time* timing — one step per time unit. Useful
for sanity tests; a realistic model would have a non-uniform mapping
(messages take Δ time, processing takes negligible time, etc.). -/
def stepIsTime : TimeMap := id

theorem stepIsTime_wellFormed : WellFormed stepIsTime := by
  refine ⟨?_, ?_⟩
  · intro i j h; exact h
  · intro T; exact ⟨T, Nat.le_refl T⟩

end TimeMap

/-! ## After-GST predicate -/

/-- "Step `i` is at or after wall-clock time `T`." -/
def StepAtOrAfter (time : TimeMap) (T : Nat) (i : Nat) : Prop :=
  time i ≥ T

/-- The earliest step `i` with `time i ≥ T`. Existence is guaranteed by
`Unbounded`. -/
theorem exists_step_after
    (time : TimeMap) (h : TimeMap.Unbounded time) (T : Nat) :
    ∃ i, StepAtOrAfter time T i :=
  h T

/-! ## Constrained Byzantine model (post-GST adversary)

Even without explicit messages, we can constrain the *trace* to forbid
unbounded delays of honest-validator commitments after GST. This is the
hook that liveness lemmas need.

`PartiallySynchronous trace time system` says: after `GST`, time advances
by at most `Δ` per step (i.e., the network/scheduler is bounded). Honest
validators' commitments thus cannot be delayed by more than `Δ` past
their wall-clock deadline.

This is the minimum constraint on the abstract model needed to state
liveness; finer-grained per-message delivery semantics await a full
network model. -/

/-- Trace `trace` together with `time` is *partially synchronous* relative
to `system` if, post-GST, each step advances time by at most `Δ`. -/
def PartiallySynchronous {S} [SystemState S]
    (system : BlockSynchroniserSystem) (_trace : Trace S) (time : TimeMap) : Prop :=
  ∀ i, time i ≥ system.GST →
    time (i + 1) ≤ time i + system.Δ

end BlockSynchroniser
