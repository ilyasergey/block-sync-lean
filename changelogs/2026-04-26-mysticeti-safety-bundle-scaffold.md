# 2026-04-26 — Mysticeti safety: bundle scaffold + belugaTrace wrappers

## What changed

Set up `Beluga/MysticetiSafetyInvariant.lean` (new file), which bundles
the four protocol-invariant hypotheses currently borne separately by
`Mysticeti/Safety.lean`'s L13 / L15:

| field | corresponds to L13/L15 hypothesis |
|---|---|
| `admission` | `h_admission : AdmissionWellFormed system state` |
| `uniqueByAuthorRound` | `h_honest_unique` (in fact stronger — drops the honesty hypothesis) |
| `noEquivocation` | `h_no_eq : NoEquivocationInParents system state` |
| `authorsValid` | `h_authors_valid` |

`belugaTrace_satisfies_mysticetiSafetyInv` proves the bundle for
`belugaTrace`. Three of four conjuncts are now sorry-free:

- `admission` — directly via `belugaTrace_admissionWellFormed`
  (already proved in `AdmissionInvariant.lean`).
- `uniqueByAuthorRound` — by `BlockInv.hasPropose` +
  `BlockInv.uniquePropose`. The honesty hypothesis is dropped because
  `uniquePropose` is total.
- `noEquivocation` — same chain (parents are themselves blocks in
  state, so `uniqueByAuthorRound_of_blockInv` applies directly).

The fourth conjunct, `authorsValid`
(`∀ B ∈ state.blocks, ∃ p ∈ system.validators, p.1 = B.author`), is
left as `sorry` and queued for delegation. It needs a separate
trace invariant about emitted operations: every
`block_propose vid B r` op has `vid` registered in
`system.validators`. Not derivable from the existing `BlockInv`
chain.

## Mysticeti/Safety.lean — belugaTrace wrappers

Added two new theorems (purely additive — existing generic L13/L15
remain in place):

- `lemma13_cert_persistence_belugaTrace` — takes only
  `(system, hids, hN, h_byz_bound, k, B, B', cert, ...)`. The four
  protocol-invariant hypotheses are discharged from the bundle.
- `lemma15_unique_cert_belugaTrace` — same shape.

L14, L16, T7 do not gain belugaTrace specialisations: their
non-trivial hypotheses are about external `view : ConsensusView` /
`order : TransactionOrder` parameters (`h_view_traceback`,
`h_decision_complete`, etc.), which are not derivable from trace
state alone.

## Why this matters

Closes the issue surfaced in conversation: `Mysticeti/Safety.lean`
imported `Beluga.AdmissionInvariant` but did not actually rely on
`belugaTrace_admissionWellFormed` to discharge its `h_admission`
hypothesis. The new wrappers make the invariant load-bearing.

Beyond admission, the bundle pattern lets us surface other folded
hypotheses cheaply: the next folding target (`authorsValid`) is
delegable as a single self-contained Aristotle round.

## Build state

`lake build` passes (6250 jobs). Sorries:
- `Beluga/MysticetiSafetyInvariant.lean`: 1 (`authorsValid`, queued).
- `Beluga/Theorems.lean`: 4 (L1/T1/T3/T4 conjuncts of bundle, in
  flight as `e8212038`).
- `Mysticeti/Liveness.lean`: 1 (Mysticeti bundle, in flight as
  `03f5fe3f`).

## What's next

1. Submit small focused Aristotle round for `authorsValid` in
   `belugaTrace_satisfies_mysticetiSafetyInv`. Frozen file:
   `Beluga/MysticetiSafetyInvariant.lean`.
2. Wait for `e8212038` (Beluga §5 noncircular bundle) and
   `03f5fe3f` (Mysticeti liveness bundle) — examine for the same
   trivialisation failure mode as `4f618efb`.
