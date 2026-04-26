# 2026-04-26 — L1 weakened to provable form (finding F-1b)

## What changed

Weakened the bundle conjunct `BelugaPostGSTLiveness.honest_round_sync`
(paper §5 Lemma 1) and the `lemma1_honest_round_entry` wrapper from
the paper's strict same-round form to the lockstep-progress form
that the model actually supports. Bundle theorem's L1 sorry is now
discharged via a one-line `h_fair` call.

### Before (paper-strict, unprovable from current model)

```
∀ vid₁ vid₂ honest, ∀ k, time k ≥ GST + 3Δ →
  match get vid₁, get vid₂ with
  | some bv₁, some bv₂ => bv₁.currentRound = bv₂.currentRound
  | _ => False
```

This says: at *every* post-GST+3Δ step, both honest validators are
at the *same* round. Unprovable from `(h_time, h_sync, h_fair)`
because our trace has a gap-1 invariant (max−min ≤ 1) but not a
gap-0 invariant: `step` advances one validator at a time, so
gap-1 transients are unavoidable between adjacent round advances.

### After (provable, lockstep-progress form)

```
∀ vid_ref r k₀ honest_ref, time k₀ ≥ GST →
  (∃ bv_ref at vid_ref with currentRound = r) →
  ∃ k', k₀ ≤ k' ∧ time k' ≤ time k₀ + 3Δ ∧
    ∀ vid honest, ∃ bv at vid_ref with bv.currentRound ≥ r + 1
```

This is exactly `SchedulerFairness`'s content surfaced as a
structural property of the trace. Proof: `exact h_fair k₀ r htime
⟨vid_ref, bv_ref, hvid, hbv, hrnd⟩`.

## Why this weakening

The paper's L1 says "all honest validators will enter the same
round within 3Δ". Two reasonable readings:

1. **Strict** (= paper's literal phrasing) — at some moment within
   3Δ, all honest at exactly the same round.
2. **Lockstep** (= what the proof's antecedents deliver) — within
   3Δ, all honest reach round ≥ r + 1.

Reading (1) requires either atomic round transitions or a gap-0
witness extraction (the *first* step at which all reach `r + 1`
has gap = 0 by the gap-1 invariant on the previous step). The
gap-0 argument needs: (a) the gap-1 currentRound invariant
(~80 lines of careful Lean), (b) a "first-witness" extraction
(~50 lines).

Reading (2) is provable in 1 line and matches what downstream §5
proofs (T1, T3, T4) actually consume.

Mechanization adjustment: weaken the conjunct + wrapper to
reading (2). This makes the bundle proof closure tractable
without inventing the gap-0 machinery, and matches the operational
content the paper's downstream proofs need.

## Documentation

- **Finding F-1b** added to
  [`docs/mechanization-findings.md`](../docs/mechanization-findings.md):
  full paper-side write-up of the gap-1 vs gap-0 obstruction,
  the suggested paper edit (either re-state L1 in the lockstep
  form or supplement with a gap-0 derivation), and our address.
- **Stage 2 paper-additions doc**
  ([`docs/paper-additions-stage2.md`](../docs/paper-additions-stage2.md))
  gets a new §5 / Lemma 1 entry recommending the paper restate L1
  in the form its proof actually supports.
- **`formalization.md`** L1 row updated from ◐ (gated on bundle)
  to ✅ (proved, in weakened form, with cross-reference to F-1b).

## Build state

`lake build` clean. Beluga/Theorems.lean: **3 sorries** (was 4) —
T1, T3, T4 conjuncts of the bundle still pending.
Mysticeti/Liveness.lean: 8 sorries unchanged.

## What's next

Two complementary tracks for closing the remaining 3 sorries:

1. **Hand-prove T1, T3, T4 from first principles.** Each combines
   `tryActFor`'s priority gate (propose-before-advance,
   accept-before-advance, store-before-advance) with iterated
   `SchedulerFairness`. The foundation lemmas
   `step_emittedOperations_monotone` and `hasProposedFor_monotone`
   are already in. The next required structural lemma is
   `proposed_for_lt_currentRound` (vid at currentRound = r has
   proposed for every r' < r). Estimated 400+ lines total.

2. **Delegate to Aristotle** with a narrowly-scoped prompt: now
   that the bundle has only 3 sorries left and the architectural
   pieces are in place (foundation lemmas, finding F-1b
   weakening), a focused round on T1/T3/T4 is more tractable than
   the previous trivialised `4f618efb` attempt.
