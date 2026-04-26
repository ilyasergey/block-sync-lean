# 2026-04-26 — Paper-consistency pass: pseudocode mapping, §5 rewrites, comment cleanup

## What changed

Post-T4, a sweep across the §5 mechanization to align with the
paper's prose, surface new findings, and document the proof
strategy in paper-faithful English.

### `Protocol.lean` — `tryActFor` ↔ paper Figure 8 mapping

Added a section header docstring above `tryActFor` that:
- Reproduces paper Figure 8 (Appendix E) `create_new_block` /
  `AC_parent_selection` / `compute_ancestors` /
  `update_score_with_watermarks` pseudocode lines 1–32.
- Tabulates the mapping from paper procedures and §4.2 prose to
  our executable definitions (`doPropose`, `doAccept`, `doStore`,
  `doAdvance`, `acParentSelection`, etc.).
- Explains the modeling choice — paper is event-driven; our
  `tryActFor` collapses to a deterministic priority order
  (propose → accept → store → advance) — and notes that this is
  faithful to the paper's claim that Beluga's guarantees do not
  depend on the event ordering.
- Lists the bits *not* in `tryActFor` (block-construction details,
  reputation update, AC parent selection) and where they live.

### `paper-additions-stage2.md` — §5 proof rewrites (new §2)

Added a section "**§5 proof rewrites: matching the mechanized
argument**" with English rewrites for L1, L2, T1, T2, T3, T4 that
faithfully capture the Lean argument. Each rewrite is roughly the
same length as the paper's existing prose proof; the originals are
preserved and contrasted in parenthetical notes.

Key paper-side recommendations surfaced by the rewrites:
- **L1, L2** rewrites are direct invocations of the post-GST
  scheduler-fairness assumption (F-1a). The paper's existing L1
  proof argues *why the assumption holds* via network-delivery
  bounds and pull; that argument belongs to the network-model
  discussion rather than to L1's deductive proof.
- **T1, T2** rewrites use the action-priority structure of
  `tryActFor` (accept ≺ store ≺ advance, parent-acceptance
  required to accept). They do not need the ImPoA-based "parents
  referenced by f+1 subsequent blocks → eventual pull" reasoning
  the paper currently uses. ImPoA remains required for the
  protocol's *runtime* but is decoupled from the *correctness*
  proofs.
- **T3, T4** rewrites use iterated L1 + the
  propose-before-advance / accept-before-advance gates and the
  parents-in-pool structural invariant of `doPropose`. T4
  specifically replaces the paper's induction-on-`r` (via T1+T2
  per round) with an induction-on-`B.r` *within* a fixed advance
  step — a tighter argument.

### `mechanization-findings.md` — F-12, F-13

Two new findings beyond Stage 1/2:

- **F-12** — §5 proof strategies: action-priority obviates
  ImPoA-based reasoning. The paper's T1/T2 proofs lean on ImPoA;
  ours don't. ImPoA remains relevant to runtime but isn't
  load-bearing for correctness. Suggested paper change: state T1
  and T2 with the action-priority argument (rewritten in Stage 2
  §2.3, §2.4); preserve ImPoA discussion in §4.3 as the
  *implementation* mechanism.

- **F-13** — Accept-store atomicity ambiguity. Paper Figure 8 line
  13 has `create_new_block` emit both `block_accept` and
  `block_store` atomically; §4 prose treats them as conceptually
  distinct outputs (different consumers in §4.4). Our mechanization
  takes the split form. Suggested paper change: pick a side
  explicitly — either collapse to a single atomic action (T1 then
  trivial) or split and use action-priority (matching our model).

### Comment cleanup in `Theorems.lean`

Removed ~12 non-essential proof-body comments that just re-stated
the next tactic in English (e.g., "two sub-cases on vid = a.1",
"vid is the actor", "Eventually trace k P := ...", "Apply causal
closure"). Substantive comments — reasons, why-it-works
explanations — kept. ~20 lines net removed.

## Build state

`lake build` clean. **Beluga/Theorems.lean: 0 sorries.**
Mysticeti/Liveness.lean: 1 sorry unchanged.

## What's next

Stage 3 of paper-additions (when §D.2 mechanization closes) will
fold any remaining findings. The §5 rewrites in Stage 2 are now
the load-bearing arguments; the original prose is preserved
alongside in the doc as a higher-level narrative.
