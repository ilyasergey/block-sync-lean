# 2026-04-25 — Planning and Aristotle setup

First entry. Project bootstrap before formalization work begins.

## Summary

- Bumped Lean toolchain to v4.28.0 (commit `aff16da`).
- Audited the existing `BlockSynchroniser/Definitions.lean` against the [Beluga paper](../docs/Block_Sync_Project.pdf).
- Drafted the formalization plan, paper mapping, and Aristotle workflow notes.
- Established the changelog convention (this file).

## What changed

### Toolchain
- `lean-toolchain`: v4.23.0 → **v4.28.0** (matches Aristotle's pinned Lean version).
- `batteries`, `mathlib`: v4.23.0 → **v4.28.0**.
- `lake-manifest.json` refreshed; mathlib cache pulled.
- `ssreflect` dependency commented out in `lakefile.lean` (manual edit by user) — the only files importing it were in `BlockSynchroniser/Existing/` and aren't part of the build target.

### Documentation (new)
- [docs/formalization-plan.md](../docs/formalization-plan.md) — overall phased plan with file layout, scope decisions, and validation strategy.
- [docs/formalization-status.md](../docs/formalization-status.md) — precise paper-to-Lean mapping with per-item status.
- [docs/aristotle-workflow.md](../docs/aristotle-workflow.md) — operational notes for delegating proofs to Aristotle.

### Aristotle integration
- Verified `aristotle` CLI works (`aristotlelib 1.0.1`); `ARISTOTLE_API_KEY` is exported in `~/.zshrc`.
- Confirmed Aristotle's pinned Lean toolchain (`v4.28.0`) matches our project — submissions should compile cleanly on their side.
- Established division of labor: structures/definitions/the-four-properties/validation by hand; pure-combinatorial and large-quorum lemmas delegated; timing/main theorems hybrid.

## Decisions locked in

| Question | Answer |
|---|---|
| Time model | `ℕ` |
| Adversary model | Quantify over arbitrary traces; honest steps must follow protocol |
| Probabilistic content | Excluded from proofs, documented as future work |
| Theorem scope | All four §5 theorems; safety bundle from Appendix D as stretch (L10, L13–16, T7) |
| Liveness side of Appendix D (L8, L9, L11, L12, T6) | Deferred — depends on timing model + pull formalization |
| Performance theorems (Appendix C: L6, L7, T5) | Out of scope — inherently probabilistic |

## Validation strategy (non-vacuity)

Every Definition-1 property is shaped `P → ∃ Q` and is satisfied by the empty trace. Defense in depth:

1. **(A)** Witness `goldenTrace` — concrete honest run with `n=4, f=1`; prove it satisfies all four properties non-trivially.
2. **(B)** `realizable_*` lemmas — antecedents are reachable in some trace.
3. **(C)** `emptyTrace`, `byzantineOnlyTrace` anti-witnesses — must fail at least one property.
4. **(D)** Optional decidability for `#eval` smoke tests.

## Next stage

Phase 0 (cleanup): revert the `state_kz` typo at `BlockSynchroniser/Definitions.lean:228`, delete `BlockSynchroniser/Existing/`, drop `blockSynchroniserValidity` and `blockSynchroniserCommonSet`, verify `lake build` is clean.
