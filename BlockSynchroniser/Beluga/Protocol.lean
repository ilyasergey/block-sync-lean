/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Beluga protocol semantics (paper §4 + Figure 8 / Appendix E).

This module unifies the data layers (state / reputation / AC / pull) into
a transition system. Two complementary characterizations:

* **`HonestStep`** — a *relational* predicate over `(s, s')` pairs.
  Captures what it means for a transition to be consistent with honest
  validator behavior. Used by Phase 5 theorems.

* **`step`** — an *executable* function that produces one valid honest
  schedule (round-robin). Used to run the protocol (`#eval`,
  `Main.lean`) and to seed concrete traces.

* **`step_refines_HonestStep`** — the bridge: every transition produced
  by `step` satisfies `HonestStep`.

Status: honest-action conditions stated; executable `step` is a
minimal honest-schedule placeholder; refinement lemma partially proved
by Aristotle round 3f (project `116385ce`) — the structural case
analysis is closed, with 5 remaining stubs documenting genuine
semantic gaps between the executable `step` and the relational
`HonestStep` spec.
-/
import Mathlib.Tactic
import BlockSynchroniser.Block
import BlockSynchroniser.System
import BlockSynchroniser.State
import BlockSynchroniser.Causal
import BlockSynchroniser.Trace
import BlockSynchroniser.Operations
import BlockSynchroniser.Beluga.State
import BlockSynchroniser.Beluga.Reputation
import BlockSynchroniser.Beluga.AdmissionControl
import BlockSynchroniser.Beluga.Pull
import BlockSynchroniser.Lib.Basic

namespace BlockSynchroniser
namespace Beluga

/-! ## Honest-action relations (paper §4.2 + Figure 8) -/

/--
Honest validator `vid` proposes a fresh round-`r` block `B` (paper §4.2;
Figure 8 lines 1–13).

Conditions:
* `vid` is honest in `system`.
* `vid` is currently in round `r` in `s`.
* `B` is well-formed: `B.author = vid`, `B.r = r`.
* `B`'s parents are the `acParentSelection` output (paper Figure 8 line 4).
* `s'` is `s` with `B` added to the global block pool and a
  `block_propose vid B r` operation appended.
-/
def HonestPropose
    (system : BlockSynchroniserSystem) (s s' : BelugaState)
    (vid : ValidatorId) (B : Block) (r : Round) : Prop :=
  isHonestValidator system vid = true ∧
  (∃ bv ∈ s.validators, bv.1 = vid ∧ bv.2.currentRound = r) ∧
  B.author = vid ∧ B.r = r ∧
  s'.blocks = B :: s.blocks ∧
  s'.emittedOperations = s.emittedOperations ++ [.block_propose vid B r]

/--
Honest validator `vid` accepts a block whose digest is `d` (paper §4.3.1;
Figure 8 line 12 `outputs block_accept`).

Conditions:
* `vid` is honest in `system`.
* The block with digest `d` is in `s.blocks`.
* `vid` has not yet output `block_accept_i(d)` (idempotence — no
  duplicate accepts).
* The block is `isAcceptableImPoA` (accepted ancestors *or* implicitly
  available).
* `s'` is `s` with `block_accept vid d` appended; per-validator state for
  `vid` updated to include `d` in `acceptedBlocks`.
-/
def HonestAccept
    (system : BlockSynchroniserSystem) (s s' : BelugaState)
    (vid : ValidatorId) (d : BlockDigest) : Prop :=
  isHonestValidator system vid = true ∧
  (∃ B ∈ s.blocks, B.d = d ∧ isAcceptableImPoA system s vid B) ∧
  ¬ HasAccepted s vid d ∧
  s'.blocks = s.blocks ∧
  s'.emittedOperations = s.emittedOperations ++ [.block_accept vid d]

/--
Honest validator `vid` stores block `B` (paper §4.3.1; Figure 8: outputs
`block_store_i(B)` once `B`'s causal history is locally available).

Conditions:
* `vid` is honest in `system`.
* `vid` has output `block_accept_i(B.d)`.
* `vid` has output `block_accept_i` for every block in `B`'s causal
  history (Definition 1.4 + ImPoA mechanism).
* `s'` is `s` with `block_store vid B` appended.
-/
def HonestStore
    (system : BlockSynchroniserSystem) (s s' : BelugaState)
    (vid : ValidatorId) (B : Block) : Prop :=
  isHonestValidator system vid = true ∧
  HasAccepted s vid B.d ∧
  (∀ B' : Block, Reaches s B B' → HasAccepted s vid B'.d) ∧
  s'.blocks = s.blocks ∧
  s'.emittedOperations = s.emittedOperations ++ [.block_store vid B]

/--
Honest validator `vid` advances from round `r` to round `r+1` (paper
§4.2 round-advancement rule (i)).

Conditions:
* `vid` is honest in `system`.
* `vid` is currently in round `r` in `s`.
* `canAdvanceByQuorum` holds (≥ `2f+1` acceptable round-`r` blocks above
  reputation threshold).
* `s'` differs only in `vid`'s `currentRound`, now `r + 1`.

Note: rule (ii) — `T_rd` timeout expires — is a wall-clock condition.
We omit it here; see formalization-status for deferred timing items.
-/
def HonestAdvance
    (system : BlockSynchroniserSystem) (s s' : BelugaState)
    (vid : ValidatorId) (r : Round) (R_L : Nat) : Prop :=
  isHonestValidator system vid = true ∧
  (∃ bv ∈ s.validators, bv.1 = vid ∧ bv.2.currentRound = r) ∧
  (∃ bv ∈ s.validators, bv.1 = vid ∧
    canAdvanceByQuorum system s bv.2.reputation vid R_L r) ∧
  s'.blocks = s.blocks ∧
  s'.emittedOperations = s.emittedOperations

/-- The validator id that produced an operation. -/
def operationAuthor : ValidatorOperation → ValidatorId
  | .block_propose vid _ _ => vid
  | .block_accept  vid _   => vid
  | .block_store   vid _   => vid

/--
**Byzantine step (refined).**

A transition `s → s'` is a *Byzantine step* iff:
* The operation log is monotonically extended (`s.emittedOperations` is a
  prefix of `s'.emittedOperations`), AND
* Every newly-emitted operation is attributable to a Byzantine validator.

Byzantine validators are otherwise unconstrained: they can propose any
block (with arbitrary parents/payload), accept any digest, or store any
block. Honest validators' operations are *not* permitted in a
Byzantine step — those flow through `HonestStep`'s four cases.
-/
def ByzantineStep (system : BlockSynchroniserSystem) (s s' : BelugaState) : Prop :=
  ∃ newOps : List ValidatorOperation,
    s'.emittedOperations = s.emittedOperations ++ newOps ∧
    ∀ op ∈ newOps, isByzantineValidator system (operationAuthor op) = true

/--
**`HonestStep`** (paper §4 protocol semantics).

A transition `s → s'` is consistent with honest behavior iff it falls
into one of the honest-action cases (propose / accept / store / advance)
*or* it is a Byzantine step.

In Phase 5 theorems, we additionally constrain `s'` to require the
honest-step witness when reasoning about honest validators' guarantees.
-/
def HonestStep
    (system : BlockSynchroniserSystem) (s s' : BelugaState) : Prop :=
  (∃ vid B r, HonestPropose system s s' vid B r) ∨
  (∃ vid d,   HonestAccept  system s s' vid d) ∨
  (∃ vid B,   HonestStore   system s s' vid B) ∨
  (∃ vid r R_L, HonestAdvance system s s' vid r R_L) ∨
  ByzantineStep system s s'

/-! ## Executable step (round-robin schedule) -/

/-- Toy injective hash: combines round and author into a unique digest.
Adequate for finite traces; replaced by a real hash if/when we extract. -/
def digest (system : BlockSynchroniserSystem) (r : Round) (vid : ValidatorId) : BlockDigest :=
  r * (system.n + 1) + vid

/-- Has validator `vid` proposed for round `r` already? -/
def hasProposedFor (s : BelugaState) (vid : ValidatorId) (r : Round) : Bool :=
  s.emittedOperations.any (fun op =>
    match op with
    | .block_propose v _ r' => v == vid && r' == r
    | _ => false)

/-- Has validator `vid` already accepted digest `d`? -/
def hasAcceptedDigest (s : BelugaState) (vid : ValidatorId) (d : BlockDigest) : Bool :=
  s.emittedOperations.any (fun op =>
    match op with
    | .block_accept v d' => v == vid && d' == d
    | _ => false)

/-- Has validator `vid` already stored digest `d`? -/
def hasStoredDigest (s : BelugaState) (vid : ValidatorId) (d : BlockDigest) : Bool :=
  s.emittedOperations.any (fun op =>
    match op with
    | .block_store v B => v == vid && B.d == d
    | _ => false)

/-- Update a single validator's local state in `s.validators`. -/
def updateValidator (s : BelugaState) (vid : ValidatorId)
    (f : BelugaValidator → BelugaValidator) : BelugaState :=
  { s with validators := s.validators.map (fun (v, bv) =>
      if v == vid then (v, f bv) else (v, bv)) }

/-- Action: `vid` proposes a fresh round-`r` block. Picks the previous round's
known blocks as parents (a simplification of `acParentSelection` — the full
reputation-based selection lands when the AC integration is exercised). -/
def doPropose (system : BlockSynchroniserSystem) (s : BelugaState)
    (vid : ValidatorId) (r : Round) : BelugaState :=
  let parentBlocks :=
    if r = 0 then []
    else (s.blocks.filter (fun B => B.r == r - 1)).map (·.d)
  let B : Block :=
    { r := r, author := vid, d := digest system r vid
      parents := parentBlocks, payload := [] }
  { s with
    blocks := B :: s.blocks
    emittedOperations := s.emittedOperations ++ [.block_propose vid B r] }

/-- Action: `vid` accepts the first known block whose digest it hasn't
accepted yet. -/
def doAccept (s : BelugaState) (vid : ValidatorId) (B : Block) : BelugaState :=
  updateValidator
    { s with emittedOperations := s.emittedOperations ++ [.block_accept vid B.d] }
    vid (fun bv => { bv with acceptedBlocks := B.d :: bv.acceptedBlocks })

/-- Action: `vid` stores a block it has accepted but not yet stored. -/
def doStore (s : BelugaState) (vid : ValidatorId) (B : Block) : BelugaState :=
  updateValidator
    { s with emittedOperations := s.emittedOperations ++ [.block_store vid B] }
    vid (fun bv => { bv with storedBlocks := B.d :: bv.storedBlocks })

/-- Action: `vid` advances from round `r` to round `r + 1`. -/
def doAdvance (s : BelugaState) (vid : ValidatorId) : BelugaState :=
  updateValidator s vid (fun bv => { bv with currentRound := bv.currentRound + 1 })

/-- All registered validators have proposed for round `r`? Used as the
honest-synchronous proxy for the AC quorum-advance condition. -/
def allProposedFor (system : BlockSynchroniserSystem) (s : BelugaState) (r : Round) : Bool :=
  system.validators.all (fun (vid, _) => hasProposedFor s vid r)

/-- Try to take an action for validator `vid` in `s`. Action priority:
propose → accept → store → advance. Returns `none` if no action applies. -/
def tryActFor (system : BlockSynchroniserSystem) (s : BelugaState)
    (vid : ValidatorId) (bv : BelugaValidator) : Option BelugaState :=
  let r := bv.currentRound
  -- 1. Propose if not yet for current round
  if !hasProposedFor s vid r then
    some (doPropose system s vid r)
  else
    -- 2. Accept any known unaccepted block
    match s.blocks.find? (fun B => !hasAcceptedDigest s vid B.d) with
    | some B => some (doAccept s vid B)
    | none =>
      -- 3. Store any accepted-but-not-stored block
      match s.blocks.find? (fun B =>
              hasAcceptedDigest s vid B.d && !hasStoredDigest s vid B.d) with
      | some B => some (doStore s vid B)
      | none =>
        -- 4. Advance round if everyone has proposed for current round
        if allProposedFor system s r then some (doAdvance s vid)
        else none

/--
**Executable round-robin step.**

Scan validators in id order; take the first applicable action (priority:
propose → accept → store → advance). If no validator can act, return `s`
unchanged (terminal / deadlock — the abstract `HonestStep` allows
`ByzantineStep` here, which is `True`).
-/
def step (system : BlockSynchroniserSystem) (s : BelugaState) : BelugaState :=
  match s.validators.findSome? (fun (vid, bv) => tryActFor system s vid bv) with
  | some s' => s'
  | none    => s

/-! ### Helper lemmas for `step_refines_HonestStep`

The three private lemmas below + the proof of `step_refines_HonestStep`
itself were filled by **Aristotle round 3f (project `116385ce`)**. See
[`docs/aristotle-attributions.md`](../../docs/aristotle-attributions.md). -/

-- proof: aristotle (project 116385ce)
/-
`hasAcceptedDigest` returning `false` implies `¬ HasAccepted`.
-/
private lemma hasAcceptedDigest_false_imp (s : BelugaState) (vid : ValidatorId)
    (d : BlockDigest) (h : hasAcceptedDigest s vid d = false) :
    ¬ HasAccepted s vid d := by
  contrapose! h;
  -- By definition of `hasAcceptedDigest`, if `HasAccepted s vid d`, then there exists an operation in `s.emittedOperations` that is `.block_accept vid d`.
  obtain ⟨op, hop⟩ : ∃ op ∈ s.emittedOperations, op = .block_accept vid d := by
    exact ⟨ _, h, rfl ⟩;
  unfold hasAcceptedDigest;
  grind

/-
`hasAcceptedDigest` returning `true` implies `HasAccepted`.
-/
private lemma hasAcceptedDigest_true_imp (s : BelugaState) (vid : ValidatorId)
    (d : BlockDigest) (h : hasAcceptedDigest s vid d = true) :
    HasAccepted s vid d := by
  contrapose! h;
  unfold hasAcceptedDigest;
  rw [ List.any_eq_false.mpr ] ; aesop;
  intro x hx; contrapose! h; unfold HasAccepted at *; aesop;

/-
If `isHonestValidator` is `false`, then `isByzantineValidator` is `true`
(assuming the validator is registered in `system.validators`).
-/
private lemma not_honest_imp_byzantine (system : BlockSynchroniserSystem)
    (vid : ValidatorId) (h : isHonestValidator system vid = false)
    (hreg : ∃ p ∈ system.validators, (p : ValidatorId × Bool).1 = vid) :
    isByzantineValidator system vid = true := by
  unfold isHonestValidator at h;
  unfold isByzantineValidator;
  unfold BlockSynchroniserSystem.isHonest at h;
  unfold BlockSynchroniserSystem.isByzantine;
  grind

/--
**Refinement lemma** — every transition produced by the executable
`step` satisfies the relational `HonestStep`.

PROVIDED SOLUTION
Unfold `step`. Case-split on the result of `findSome?`:

* **No validator can act** (`step s = s`): take `ByzantineStep` with
  `newOps = []`. The op log is unchanged, the constraint vacuously
  holds.
* **Validator `vid` (honest) takes action**: case-split on which action
  `tryActFor` chose (propose / accept / store / advance). Each branch
  constructs the corresponding `HonestPropose` / `HonestAccept` /
  `HonestStore` / `HonestAdvance` existential.
* **Validator `vid` (Byzantine) takes action**: take `ByzantineStep`
  with `newOps = [the new operation]`. The op log gained exactly one
  operation by `vid`, and `vid` is Byzantine.

Currently `tryActFor` does not check honesty before acting, so a
Byzantine validator could be picked even when honest validators have
nothing to do; that's why the Byzantine branch is needed. A future
refinement could constrain `step` to skip Byzantine validators, after
which only the honest cases apply.
-/
-- proof: aristotle (project 116385ce) — partial; 5 inline sorries are
-- semantic / well-formedness gaps documented in aristotle-attributions.md
theorem step_refines_HonestStep
    (system : BlockSynchroniserSystem) (s : BelugaState) :
    HonestStep system s (step system s) := by
  simp only [step]
  -- Case-split the outer match (findSome?) in the goal
  split
  · -- some s' branch: a validator took action
    rename_i s' hfind
    -- Extract the active validator witness via Lib.findSome_witness
    obtain ⟨⟨vid, bv⟩, hmem, htry⟩ := Lib.findSome_witness _ _ _ hfind
    -- Case-split tryActFor into its four branches
    simp only [tryActFor] at htry
    by_cases hprop : hasProposedFor s vid bv.currentRound = true
    · -- ── Already proposed → accept / store / advance ──────────────────
      simp only [hprop, Bool.not_true] at htry
      match hacc : s.blocks.find? (fun B => !hasAcceptedDigest s vid B.d) with
      | some B_acc =>
        -- ── Accept branch ─────────────────────────────────────────────
        simp only [hacc] at htry
        have heq : s' = doAccept s vid B_acc := Option.some.inj htry.symm
        subst heq
        by_cases hhon : isHonestValidator system vid = true
        · -- Honest → HonestAccept
          right; left; use vid, B_acc.d
          constructor; · exact hhon
          constructor
          · exact ⟨B_acc, List.mem_of_find?_eq_some hacc, rfl, by sorry⟩
          constructor
          · exact hasAcceptedDigest_false_imp s vid B_acc.d
              (by have := List.find?_some hacc
                  simp at this; exact this)
          exact ⟨by simp [doAccept, updateValidator],
                  by simp [doAccept, updateValidator]⟩
        · -- Byzantine → ByzantineStep
          right; right; right; right
          exact ⟨[.block_accept vid B_acc.d],
            by simp [doAccept, updateValidator],
            fun op hop => by
              simp at hop; subst hop; simp [operationAuthor]; sorry⟩
      | none =>
        simp only [hacc] at htry
        match hstore : s.blocks.find? (fun B =>
            hasAcceptedDigest s vid B.d && !hasStoredDigest s vid B.d) with
        | some B_store =>
          -- ── Store branch ──────────────────────────────────────────────
          simp only [hstore] at htry
          have heq : s' = doStore s vid B_store := Option.some.inj htry.symm
          subst heq
          by_cases hhon : isHonestValidator system vid = true
          · -- Honest → HonestStore
            right; right; left; use vid, B_store
            have hspec := List.find?_some hstore
            simp [Bool.and_eq_true] at hspec
            constructor; · exact hhon
            constructor
            · exact hasAcceptedDigest_true_imp s vid B_store.d hspec.1
            constructor
            · -- Causal history condition: not checked by executable
              sorry
            exact ⟨by simp [doStore, updateValidator],
                    by simp [doStore, updateValidator]⟩
          · -- Byzantine → ByzantineStep
            right; right; right; right
            exact ⟨[.block_store vid B_store],
              by simp [doStore, updateValidator],
              fun op hop => by
                simp at hop; subst hop; simp [operationAuthor]; sorry⟩
        | none =>
          -- ── Advance / none branch ───────────────────────────────────
          simp only [hstore] at htry
          by_cases hadv : allProposedFor system s bv.currentRound = true
          · -- Advance → ByzantineStep with [] (no ops emitted)
            simp only [hadv, ↓reduceIte] at htry
            have heq : s' = doAdvance s vid := Option.some.inj htry.symm
            subst heq
            right; right; right; right
            exact ⟨[], by simp [doAdvance, updateValidator], by simp⟩
          · -- No action possible → contradiction with `some s'`
            simp at htry
            rw [show allProposedFor system s bv.currentRound = false from
              Bool.eq_false_iff.mpr hadv] at htry
            simp at htry
    · -- ── Not yet proposed → Propose branch ───────────────────────────
      simp only [Bool.not_eq_true] at hprop
      simp only [hprop, Bool.not_false, ↓reduceIte] at htry
      have heq : s' = doPropose system s vid bv.currentRound :=
        Option.some.inj htry.symm
      subst heq
      by_cases hhon : isHonestValidator system vid = true
      · -- Honest → HonestPropose
        left
        exact ⟨vid,
          { r := bv.currentRound, author := vid,
            d := digest system bv.currentRound vid,
            parents := if bv.currentRound = 0 then [] else
              (s.blocks.filter (fun B => B.r == bv.currentRound - 1)).map (·.d),
            payload := [] },
          bv.currentRound, hhon,
          ⟨(vid, bv), hmem, rfl, rfl⟩, rfl, rfl,
          by simp [doPropose], by simp [doPropose]⟩
      · -- Byzantine → ByzantineStep
        right; right; right; right
        show ByzantineStep system s (doPropose system s vid bv.currentRound)
        unfold doPropose
        use [.block_propose vid { r := bv.currentRound, author := vid, d := digest system bv.currentRound vid, parents := if bv.currentRound = 0 then [] else (s.blocks.filter (fun b => b.r == bv.currentRound - 1)).map (·.d), payload := [] } bv.currentRound]
        exact ⟨by simp, fun op hop => by simp at hop; subst hop; simp [operationAuthor]; sorry⟩
  · -- none branch: no validator can act → ByzantineStep with newOps = []
    right; right; right; right
    exact ⟨[], by simp, by simp⟩

/--
The Beluga-induced trace at step `n` (paper §4 protocol unrolled).

`belugaTrace system 0 = BelugaState.init system`; subsequent states are
produced by iterating `step`. Phase 5's main theorems are stated
against `belugaTrace`.
-/
def belugaTrace (system : BlockSynchroniserSystem) : Trace BelugaState :=
  fun n => Nat.rec (BelugaState.init system) (fun _ s => step system s) n

end Beluga
end BlockSynchroniser