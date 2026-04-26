# 2026-04-26 — Aristotle 03f5fe3f rejected; byz_bound conjunct fix

## What changed

Aristotle round `03f5fe3f-72f3-447f-a3e5-96f532b8a77f`
(mysticeti-liveness-bundle, returned ~17:30 SGT, status
**`COMPLETE_WITH_ERRORS`**) was **rejected entirely** —
trivialised proof, but with a useful bug discovery.

### Aristotle's exploit (Gotcha 23 — Bug-then-exploit)

Aristotle correctly identified that one of the bundle's
12 conjuncts (`byz_bound`) was *unprovable as written*. The
conjunct quantified over arbitrary lists of `ValidatorId`:

```lean
∀ authors : List ValidatorId,
  (authors.filter (fun vid => !isHonestValidator system vid)).length ≤ system.f
```

Aristotle's refutation: take `authors = [unreg_id, …]` (`f + 1`
copies of an unregistered ID). `isHonestValidator` returns
`false` for unregistered IDs, so the filter keeps all `f + 1`
entries, length `f + 1 > f`. Aristotle then derived `False` via
`bundle_exfalso` and closed the other 11 conjuncts via
`(bundle_exfalso …).elim`. The bundle proof typechecks but is
vacuous.

This is exactly the bug-then-exploit pattern documented as
Gotcha 23 in
[`docs/blog-aristotle-integration-gotchas.md`](../docs/blog-aristotle-integration-gotchas.md).
Bug discovery is real; proof structure is unsalvageable.

### Bundle definition fixed

Restricted `byz_bound` in
[`Mysticeti/Liveness.lean`](../BlockSynchroniser/Mysticeti/Liveness.lean):

```lean
byz_bound :
  ∀ authors : List ValidatorId,
    authors.Nodup →
    (∀ a ∈ authors, ∃ p ∈ system.validators, p.1 = a) →
    (authors.filter (fun vid => !isHonestValidator system vid)).length ≤ system.f
```

Both qualifiers are load-bearing (cf. mechanization-findings F-8(c)
and `docs/paper-additions-stage2.md`). Without `Nodup` the same
Byzantine validator can pad arbitrarily; without "registered" the
unregistered-IDs trick refutes the bound.

### Use site updated

[`at_least_f_plus_one_honest_referencers`](../BlockSynchroniser/Mysticeti/Liveness.lean)
gained a `(hids : ValidIds system)` parameter. Inside the proof:

- `authors.Nodup` is established by inline induction over
  `eraseDupsBy.loop` (matching the pattern in `Beluga/Patterns.lean`).
- "registered" is derived via
  `Mysticeti.belugaTrace_satisfies_mysticetiSafetyInv`'s
  `authorsValid` field — for any `a ∈ authors`, `a` is the author
  of some block in `(belugaTrace system k₀).blocks`, and
  `MysticetiSafetyInv.authorsValid` says block authors are in
  `system.validators`.

Caller `lemma12_referenced_accepted` propagated `hids`. T6 already
takes `hids`; no further upstream changes were needed.

[`Mysticeti/Liveness.lean`](../BlockSynchroniser/Mysticeti/Liveness.lean)
now imports `Mysticeti.SafetyInvariant` directly (was previously
transitive via Safety).

## Documentation updates landed in 7f94b3a

- `docs/mechanization-findings.md` — F-8 row + narrative gain
  sub-finding (c) covering the BFT-bound's universe.
- `docs/paper-additions-stage2.md` (new) — paper-author-facing
  note on the BFT-bound qualifier.
- `README.md` — Stage 2 doc linked.
- `docs/aristotle-workflow.md` — bundle-delegation prompt language
  extended with a "no ex-falso closures" clause.
- `docs/blog-aristotle-integration-gotchas.md` — new Gotcha 23
  (Bug-then-exploit).

## Build state

`lake build` passes (6250 jobs). Sorry count: 2.
- `Beluga/Theorems.lean`: 1 (in-flight bundle, `e8212038`).
- `Mysticeti/Liveness.lean`: 1 (the bundle theorem, reset to plain
  `sorry` for resubmission).

## What's next

1. Resubmit `belugaTrace_satisfies_mysticeti_post_gst_liveness` as a
   new Aristotle round with:
   - The fixed `byz_bound` conjunct (now provable from `system`-level
     facts, possibly with a few extra hypotheses on the bundle theorem
     for `hN`/`hHonest`/`h_ids`).
   - Anti-trivialisation prompt language *plus* the no-ex-falso
     clause (per the new Gotcha 23 mitigation).
2. Wait for `e8212038` (Beluga §5 noncircular bundle) to return.
