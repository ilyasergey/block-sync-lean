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

Status: structural skeleton. Honest-action conditions are stated; the
executable `step` is a minimal honest-schedule placeholder; the
refinement lemma carries a `PROVIDED SOLUTION` sketch and is `sorry`'d
for a future sub-phase (or Aristotle round).
-/
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
theorem step_refines_HonestStep
    (system : BlockSynchroniserSystem) (s : BelugaState) :
    HonestStep system s (step system s) := by
  unfold step
  generalize hf :
    s.validators.findSome? (fun p => tryActFor system s p.1 p.2) = result
  cases result with
  | none =>
    -- step s = s. Use ByzantineStep with newOps = [].
    show HonestStep system s s
    right; right; right; right
    refine ⟨[], ?_, ?_⟩
    · simp
    · intro op hop
      cases hop
  | some s' =>
    -- step s = s'. The full case analysis (extracting (vid, bv) from
    -- findSome?, splitting on tryActFor's four branches, and on validator
    -- honesty) is non-trivial Lean tactic plumbing. Sketched in the
    -- docstring; queued for Aristotle round 3.
    sorry

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
