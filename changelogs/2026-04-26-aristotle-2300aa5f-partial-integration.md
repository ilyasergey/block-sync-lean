# 2026-04-26 — Aristotle 2300aa5f (mysticeti-liveness retry), partial integration

## What changed

Integrated Aristotle project `2300aa5f-5db8-467d-a007-c10380717265`
(mysticeti-liveness-bundle-no-exfalso, returned ~21:00 SGT, status
**`COMPLETE_WITH_ERRORS`**). Resubmission after `03f5fe3f`'s
ex-falso trivialisation (Gotcha 23). This round respected the
prompt constraints — no trivialisation — but left the deep
post-GST liveness work undone.

### What Aristotle did (kept)

1. **`byz_bound_of_system_constraints`** — sorry-free helper
   lemma proving that any nodup list of *registered* validators
   has at most `f` non-honest entries. About 30 lines using
   `Finset.card_le_card`, `BlockSynchroniserSystem.validatorCountCorrect`,
   and direct manipulation of the validator-list partition. This
   discharges the bundle's `byz_bound` conjunct.

2. **Architectural restructure** — moved `hN`, `hHonest`,
   `h_ids` from bundle conjuncts to theorem hypotheses on
   `belugaTrace_satisfies_mysticeti_post_gst_liveness`. They are
   *system constraints*, not trace invariants preserved by
   `step` — the right home is hypotheses on the bundle theorem.
   The bundle structure itself still carries them as conjuncts
   (trivially passed through), so wrapper lemmas continue to
   project from the bundle without changes.

3. **Plumbing through 15 downstream lemmas** — every wrapper /
   helper that ultimately calls
   `belugaTrace_satisfies_mysticeti_post_gst_liveness` now takes
   `hN`, `hHonest`, `h_ids` and passes them through.
   `at_least_f_plus_one_honest_referencers` retains the `hids`
   parameter we added in commit `34908c7`.

4. **Anti-trivialisation discipline** — no ex-falso closures,
   no circular hypotheses. The prompt's Gotcha 22 + 23
   constraints held. (First round to validate the strengthened
   anti-trivialisation prompt language landed in commit
   `28f774f`.)

### What Aristotle did *not* do (8 remaining sorries)

The bundle theorem now has 8 individual `sorry` fields — one per
genuine post-GST liveness conjunct. These are paper §D.2 deep
properties requiring real inductive trace analysis:

| Conjunct | Paper origin |
|---|---|
| `honest_round_entry` | L1 (3Δ round-entry post-GST) |
| `leader_propose` | §4.2 honest-leader discipline |
| `honest_ref_leader` | L8 (leader block referenced next round) |
| `honest_certify_leader` | L9 (honest leader certified) |
| `three_consec_commit` | L10 + direct-decide rule |
| `backward_induction` | indirect-decide rule |
| `block_pull_liveness` | §4.3 ImPoA pull |
| `honest_eventually_accepts` | §4.3 availability propagation |

The honest framing: the **load-bearing question** (does Beluga's
trace actually deliver post-GST liveness?) is *not* answered.
Theorems L8, L9, L11, L12, T6 remain transitively gated on these
8 sorries.

### Why we kept this round anyway

- The architectural fix is correct and we'd need to redo it
  regardless.
- `byz_bound_of_system_constraints` is real, integrable work
  (saves a future round on that conjunct).
- The 8 sorries are now *individually nameable*, so we can
  submit them as 8 narrowly-scoped rounds (or 2-3 grouped) rather
  than re-attempting the whole 12-conjunct bundle.

### Provenance markers added

- `byz_bound_of_system_constraints`: marked
  `-- proof: aristotle (project 2300aa5f) — mysticeti-liveness-bundle-no-exfalso round`.
- `belugaTrace_satisfies_mysticeti_post_gst_liveness`: same
  marker, with note "(system-constraint scaffolding + byz_bound
  proof; 8 liveness conjuncts pending)".

## Build state

`lake build` passes. Sorry count: **12** (unchanged in net
across the project, but rebalanced):
- `Beluga/Theorems.lean`: 4 (in-flight bundle, `e8212038`).
- `Mysticeti/Liveness.lean`: 8 (the 8 individually-named
  liveness conjuncts of the bundle).

Pre-integration the project had: 4 (Beluga) + 1 (Mysticeti
bundle theorem). Post-integration: 4 (Beluga) + 8 (Mysticeti
bundle's individual sorries). Net +7 in *visible* sorry count,
but the underlying proof work that needs to land is the same —
just made explicit.

## What's next

1. **Submit narrow rounds for the 8 liveness conjuncts.** Likely
   2-3 grouped submissions:
   - L1-derived: `honest_round_entry`, `leader_propose`,
     `honest_ref_leader`, `honest_certify_leader`. Group on
     "round/leader/reference-block timing post-GST".
   - Decision-flow: `three_consec_commit`, `backward_induction`.
     Group on "commit-decision propagation".
   - Pull/accept: `block_pull_liveness`,
     `honest_eventually_accepts`. Group on "block availability".
   Each subset has shared infrastructure; per Gotcha 21 the
   bundle-then-delegate pattern still applies, but the 12-conjunct
   bundle was too wide for one round.
2. Wait for `e8212038` (Beluga §5 noncircular bundle) to
   return; integrate.

## Aristotle attribution

Project `2300aa5f-5db8-467d-a007-c10380717265` — full attribution
appended to
[`docs/aristotle-attributions.md`](../docs/aristotle-attributions.md).
