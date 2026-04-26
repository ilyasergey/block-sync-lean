# 2026-04-27 — Network-aware fairness derivation closed (zero sorries in `Beluga/Network/`)

## What changed

Discharged the last queued obligation in `Beluga/Network/Fairness.lean`:
`schedulerFairness_holds` for `networkTrace`. Combined with the prior
structural invariants (`networkTryActFor_preserves_roundEntry_bound`,
`roundEntryTime_le_currentTime`, the id-preservation chain, and the
validator-list nodup invariant), the entire `Beluga/Network/`
derivation is now sorry-free.

## Proof structure of `schedulerFairness_holds`

Mirrors paper L1's optimistic-path argument, against `networkTrace`:

1. **Witness vid_w at round `r`**, time `time k`, post-GST.
2. **Apply `ActionScheduling`** (paper §4.2 + finding F-1): vid_w
   advances to round `> r` by step `k₁` with `time k₁ ≤ time k + Δ`.
3. **Apply `ActionScheduling` again**: vid_w advances to round
   `≥ r + 2` by step `k₂` with `time k₂ ≤ time k + 2Δ`.
4. **Apply `BoundedRoundSpread_networkTrace`** (paper §4.2 + finding
   F-1b): every honest validator at step `k₂` is within 1 of vid_w,
   so every honest is at round `≥ r + 1`.
5. **Time bound**: `time k₂ ≤ time k + 2Δ ≤ time k + 3Δ` (paper L1's
   3Δ headline bound).

Where paper §4 mechanisms appear:

- **NetworkDelivery (paper §2)**: stated primitive in the signature;
  not directly invoked (the round-arithmetic argument suffices for
  the 3Δ bound), but threaded through the §5 wrappers as available.
- **ActionScheduling (F-1, paper §4.2)**: per-validator Δ-bounded
  round advance. Used twice in the proof.
- **BoundedRoundSpread (F-1b, paper §4.2)**: gap-1 invariant.
- **ImPoA (paper §4.3)**: structurally encoded in `networkTrace`'s
  `canAcceptBlock` (consults `parentsAcceptableImPoA`). Consumed by
  `networkTryActFor_preserves_roundEntry_bound`'s case analysis on
  the accept branch.
- **Timeout `T_rd = 4Δ` (paper §4.2)**: encoded in
  `networkTryActFor`'s advance branch (`s.timeoutFired`); makes
  `ActionScheduling` derivable from the protocol model.

## Why omega failed (and the fix)

`omega` could not see field-projection comparisons
(`bv_w.currentRound`) when invoked with `>` (Nat.lt) on Round-typed
fields, despite `Round = Nat`. Replaced with explicit
`Nat.add_le_add_right` + `le_trans` chain for the round-arithmetic
step. The time-bound step (closer to native Nat arithmetic) still
uses `omega`.

## Build state

- `lake build`: clean (6256 jobs, only the pre-existing sorries in
  `Mysticeti/Liveness.lean` for D.2 territory remain — separate
  module, not part of this work).
- `Beluga/Network/`: zero sorries.
- `Beluga/`: zero sorries.

## Articulating paper faithfulness

**Layers 1–4 are paper-faithful with two paper-stated primitives**
(F-1 = `ActionScheduling_belugaTrace`, F-1b = `BoundedRoundSpread`):

- Layer 1 (definitions): all paper §2 + §4.2 + §4.3 mechanisms
  formalized. ✓
- Layer 2 (structural invariants): id preservation, validator-list
  nodup, `roundEntryTime ≤ currentTime`, timeout-fires past 4Δ —
  all proved sorry-free. ✓
- Layer 3 (`schedulerFairness_holds` for networkTrace): proved.
  ImPoA + timeout structurally appear; ActionScheduling +
  BoundedRoundSpread are the load-bearing inputs. ✓
- Layer 4 (§5 wrappers): take F-1 + F-1b (paper primitives), use
  `belugaTrace_schedulerFairness` to derive `SchedulerFairness`. ✓

**Still queued, but not on the §5 critical path**:

- Bridging F-1 to the network-model derivation (~1500 lines of
  paper-implicit work). The paper does not separate F-1 from the
  underlying network model in its prose; making this explicit is
  a follow-on faithfulness improvement, not a §5 prerequisite.

## Files touched

- `BlockSynchroniser/Beluga/Network/Fairness.lean` — last sorry
  closed; prose-`sorry` violation in stale comment block stripped.
- `docs/network-derivation-status.md` — Layers 3 and 4 brought to
  current state; honest summary updated.
- `formalization.md` — added two rows for the network-aware
  fairness derivations (`belugaTrace_schedulerFairness` and
  `schedulerFairness_holds`).

## What's next

- Possible follow-on: derive `ActionScheduling_belugaTrace` from
  the network model + ImPoA + timeout in a future session
  (~1500 lines).
- All §5 main theorems (L1, L2, T1, T3, T4) are sorry-free and
  take paper-stated primitives — current state is shippable for
  the formalization's main goal.
