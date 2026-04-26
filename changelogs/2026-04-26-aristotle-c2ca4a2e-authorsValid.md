# 2026-04-26 — Aristotle c2ca4a2e (mysticeti-safety-authorsValid), clean integration

## What changed

Integrated Aristotle project `c2ca4a2e-8323-448c-9c47-61bf28aa7f6e`
(mysticeti-safety-authorsValid round, returned ~18:35 SGT, status
**`COMPLETE`** — clean, no `_WITH_ERRORS`).

The single sorry'd `authorsValid` conjunct of
`belugaTrace_satisfies_mysticetiSafetyInv` is now closed.
`Beluga/MysticetiSafetyInvariant.lean` is sorry-free.

### Inductive carrier strengthening — the right move

Aristotle proved `authorsValid` for `belugaTrace` by Nat induction
on `k`, but with a private auxiliary lemma `authorsValid_trace`
whose statement is the *joint* invariant
`(∀ B ∈ blocks, ...) ∧ (∀ vid ∈ validators.map Prod.fst, ...)`.
The two-conjunct carrier is what makes the induction go through:
proving `authorsValid` alone is not self-sufficient because the
`doPropose` step adds a block whose author is `vid` taken from
`s.validators`, and to lift "`vid ∈ s.validators` IDs" to
"`vid ∈ system.validators` IDs" you need the second conjunct.

This is **exactly** the bundle-strengthening pattern that
Gotcha 21 + Gotcha 22 prescribe. Aristotle did it correctly,
without introducing any theorem-level hypothesis matching the
conclusion (Gotcha 22's anti-trivialisation rule held).

### Helper lemmas added (11)

All marked `-- proof: aristotle (project c2ca4a2e)`:

| Lemma | What it says |
|---|---|
| `updateValidator_validators_map_fst` | `updateValidator` preserves validator-ID list |
| `doAccept_validators_map_fst` | `doAccept` preserves validator IDs |
| `doStore_validators_map_fst` | `doStore` preserves validator IDs |
| `doAdvance_validators_map_fst` | `doAdvance` preserves validator IDs |
| `doPropose_validators_map_fst` | `doPropose` preserves validator IDs |
| `doAccept_blocks` | `doAccept` doesn't change blocks |
| `doStore_blocks` | `doStore` doesn't change blocks |
| `doAdvance_blocks` | `doAdvance` doesn't change blocks |
| `doPropose_blocks` | `doPropose` prepends one block with `author = vid` |
| `step_blocks_mem` | every block in `step system s` is either in `s.blocks` or has author in validators |
| `init_validators_ids` | initial state's validator IDs come from `system.validators` |

### Integration fixes

Three Gotcha-flavored issues with Aristotle's tarball, all fixed
during integration:

1. **Gotcha 1** — Aristotle added `import Mathlib`. Narrowed to
   `import Mathlib.Tactic` to keep the linker arg-list bounded.
2. **Gotcha 2** — Aristotle left 4 `exact?` placeholders:
   - `doAccept_blocks`, `doStore_blocks`, `doAdvance_blocks` —
     each replaced with `unfold ...; rfl`.
   - The base case of `authorsValid_trace`'s validators conjunct
     — replaced with `init_validators_ids` (extracted as a
     standalone lemma).
3. **Provenance markers** — added `-- proof: aristotle (project c2ca4a2e)`
   above each Aristotle-introduced lemma.

## Significance

This was the first delegation round to test Gotcha 22's
anti-trivialisation prompt language: *"Do NOT add any theorem
hypothesis whose statement is equal to one of the bundle conjuncts;
you MAY extend the structure with extra carrier conjuncts as long
as inductively provable from `belugaTrace` alone."*

Result was textbook: Aristotle correctly distinguished the two
cases — kept the theorem signature unchanged (no
trivialising hypothesis on the public theorem), but introduced an
internal joint-invariant carrier that was strictly stronger than
the target conjunct. That's the right pattern.

Recommend embedding this prompt language in
[`docs/aristotle-workflow.md`](../docs/aristotle-workflow.md)
as the default phrasing for bundle-style delegations going forward.

## Build state

`lake build` passes (6250 jobs). Sorry count: **5** (down from 6
this morning). Remaining sorries:
- `Beluga/Theorems.lean`: 4 conjuncts of the in-flight Beluga §5
  bundle (`e8212038`).
- `Mysticeti/Liveness.lean`: 1 (the in-flight Mysticeti liveness
  bundle, `03f5fe3f`).

## What's next

1. (Per user request, separate commit) Move
   `BlockSynchroniser/Beluga/MysticetiSafetyInvariant.lean` →
   `BlockSynchroniser/Mysticeti/SafetyInvariant.lean` and
   restate the namespace as `Mysticeti`. Updates all references
   (root module, Safety.lean import, formalization.md links,
   tracker docs).
2. Wait for `e8212038` and `03f5fe3f` to return; integrate.
