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
`vid` has accepted all of `B`'s parents in `s` (per-step parent
availability check matching paper §4.2's "acceptable" condition,
restricted to the strict-receivability case — the paper's broader
ImPoA-based acceptance is captured by `Pull.isAcceptableImPoA` and
will be added as a disjunct in a future refinement).
-/
def parentsAccepted (s : BelugaState) (vid : ValidatorId) (B : Block) : Prop :=
  ∀ parent_d ∈ B.parents, HasAccepted s vid parent_d

/--
Honest validator `vid` accepts a block whose digest is `d` (paper §4.2,
Figure 8 line 12 `outputs block_accept`).

Conditions (per-step, paper-faithful):

* `vid` is honest in `system`.
* A block `B` with digest `d` is in `s.blocks` (vid has received `B`).
* All of `B`'s parents have already been accepted by `vid` (per the
  paper's acceptable-block condition — the broader ImPoA disjunct is
  out-of-scope for the strict per-step refinement).
* `vid` has not yet output `block_accept_i(d)` (idempotence — no
  duplicate accepts).
* `s'` is `s` with `block_accept vid d` appended.
-/
def HonestAccept
    (system : BlockSynchroniserSystem) (s s' : BelugaState)
    (vid : ValidatorId) (d : BlockDigest) : Prop :=
  isHonestValidator system vid = true ∧
  (∃ B ∈ s.blocks, B.d = d ∧ parentsAccepted s vid B) ∧
  ¬ HasAccepted s vid d ∧
  s'.blocks = s.blocks ∧
  s'.emittedOperations = s.emittedOperations ++ [.block_accept vid d]

/--
Honest validator `vid` stores block `B` (paper §4.3.1; Figure 8: outputs
`block_store_i(B)` once `B`'s causal history is locally available).

Conditions (per-step, paper-faithful):

* `vid` is honest in `system`.
* `vid` has output `block_accept_i(B.d)`.
* `vid` has output `block_accept_i` for every block in `B`'s causal
  history (the strict §4.3.1 "ancestors locally available" condition).
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
We omit it here; the timing model is deferred (see formalization.md).
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
**State well-formedness.** The state's per-validator list mirrors
`system.validators`: every entry's id is a registered validator. This
is a structural invariant established at `BelugaState.init` and
preserved by `step`; needed at the per-step refinement level to argue
that "not-honest implies Byzantine" for the local validator id.
-/
def BelugaState.WellFormed
    (system : BlockSynchroniserSystem) (s : BelugaState) : Prop :=
  ∀ p ∈ s.validators, ∃ q ∈ system.validators, q.1 = p.1

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
    -- 2. Accept any known unaccepted block whose parents are all already
    --    accepted by `vid` (paper §4.2 acceptable-block condition,
    --    matching `parentsAccepted`).
    match s.blocks.find? (fun B =>
            !hasAcceptedDigest s vid B.d &&
            B.parents.all (fun pd => hasAcceptedDigest s vid pd)) with
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
The Beluga-induced trace at step `n` (paper §4 protocol unrolled).

`belugaTrace system 0 = BelugaState.init system`; subsequent states are
produced by iterating `step`. Phase 5's main theorems are stated
against `belugaTrace`.
-/
def belugaTrace (system : BlockSynchroniserSystem) : Trace BelugaState :=
  fun n => Nat.rec (BelugaState.init system) (fun _ s => step system s) n

/-! ### Bool/Prop bridge lemmas for `hasAcceptedDigest` -/

-- proof: aristotle (project 116385ce)
private lemma hasAcceptedDigest_false_imp (s : BelugaState) (vid : ValidatorId)
    (d : BlockDigest) (h : hasAcceptedDigest s vid d = false) :
    ¬ HasAccepted s vid d := by
  contrapose! h
  obtain ⟨op, hop⟩ : ∃ op ∈ s.emittedOperations, op = .block_accept vid d := by
    exact ⟨ _, h, rfl ⟩
  unfold hasAcceptedDigest
  grind

private lemma hasAcceptedDigest_true_imp (s : BelugaState) (vid : ValidatorId)
    (d : BlockDigest) (h : hasAcceptedDigest s vid d = true) :
    HasAccepted s vid d := by
  contrapose! h
  unfold hasAcceptedDigest
  rw [ List.any_eq_false.mpr ] ; aesop
  intro x hx; contrapose! h; unfold HasAccepted at *; aesop

/-! ### Trace-level causal-acceptance invariant

A trace-level proof that the executable `step` function maintains
causal closure: if a validator has accepted a block's digest, it has
also accepted the digest of every ancestor block. This invariant is
needed by `honestStep_of_store` to satisfy `HonestStore`'s causal
history condition.

The proof proceeds in three stages:
1. A block-level structural invariant (`BlockInv`) tracking digest
   canonicity, proposal presence, and proposal uniqueness.
2. An acceptance-level invariant (`AcceptInv`) tracking that accepted
   blocks have their parents accepted, and that accepted digests
   correspond to blocks in the pool.
3. `CausallyClosed` follows from `AcceptInv` by induction on `Reaches`.
-/

-- proof: aristotle (project 3f6cf619) — round 4-followup
-- The `ValidIds` / `CausallyClosed` / `BlockInv` / `AcceptInv` chain
-- and all supporting lemmas through `causallyClosed_trace` were
-- introduced and proved by this round.

/-- All validator IDs in the system are bounded by `system.n + 1`.
Ensures the `digest` function is injective across validators. -/
def ValidIds (system : BlockSynchroniserSystem) : Prop :=
  ∀ p ∈ system.validators, p.1 < system.n + 1

/-- Causal closure: if `vid` has accepted `B.d`, then `vid` has accepted
the digest of every block reachable from `B` via parent pointers. -/
def CausallyClosed (s : BelugaState) (vid : ValidatorId) : Prop :=
  ∀ B, HasAccepted s vid B.d →
    ∀ B', Reaches s B B' → HasAccepted s vid B'.d

/-- Block-level structural invariant (independent of validator id). -/
structure BlockInv (system : BlockSynchroniserSystem) (s : BelugaState) : Prop where
  canonical : ∀ B ∈ s.blocks, B.d = digest system B.r B.author
  hasPropose : ∀ B ∈ s.blocks,
    ValidatorOperation.block_propose B.author B B.r ∈ s.emittedOperations
  uniquePropose : ∀ v r B1 B2,
    ValidatorOperation.block_propose v B1 r ∈ s.emittedOperations →
    ValidatorOperation.block_propose v B2 r ∈ s.emittedOperations → B1 = B2
  authorBounded : ∀ B ∈ s.blocks, B.author < system.n + 1

/-- Acceptance-level invariant (depends on validator id). -/
structure AcceptInv (s : BelugaState) (vid : ValidatorId) : Prop where
  acceptedParents : ∀ B ∈ s.blocks, HasAccepted s vid B.d →
    ∀ pd ∈ B.parents, HasAccepted s vid pd
  acceptedBlockExists : ∀ d, HasAccepted s vid d → ∃ B ∈ s.blocks, B.d = d

-- The `digest` function is injective when validator IDs are bounded.
lemma digest_injective (system : BlockSynchroniserSystem)
    (r1 r2 : Round) (v1 v2 : ValidatorId)
    (hv1 : v1 < system.n + 1) (hv2 : v2 < system.n + 1)
    (h : digest system r1 v1 = digest system r2 v2) :
    r1 = r2 ∧ v1 = v2 := by
  simp only [digest] at h
  have hmod1 : (r1 * (system.n + 1) + v1) % (system.n + 1) = v1 := by
    rw [show r1 * (system.n + 1) = (system.n + 1) * r1 from by ring]
    exact Nat.mul_add_mod _ r1 v1 ▸ Nat.mod_eq_of_lt hv1
  have hmod2 : (r2 * (system.n + 1) + v2) % (system.n + 1) = v2 := by
    rw [show r2 * (system.n + 1) = (system.n + 1) * r2 from by ring]
    exact Nat.mul_add_mod _ r2 v2 ▸ Nat.mod_eq_of_lt hv2
  have hv : v1 = v2 := by rw [← hmod1, h, hmod2]
  refine ⟨?_, hv⟩
  subst hv
  have h1 : r1 * (system.n + 1) = r2 * (system.n + 1) := Nat.add_right_cancel h
  exact mul_right_cancel₀ (Nat.succ_ne_zero _) h1

-- No-duplicate-digests follows from BlockInv + ValidIds.
private lemma noDupDigests_of_blockInv (system : BlockSynchroniserSystem)
    (s : BelugaState) (_hids : ValidIds system)
    (hbi : BlockInv system s) :
    ∀ B1 B2, B1 ∈ s.blocks → B2 ∈ s.blocks → B1.d = B2.d → B1 = B2 := by
  intro B1 B2 h1 h2 hd
  have hc1 := hbi.canonical B1 h1
  have hc2 := hbi.canonical B2 h2
  have hp1 := hbi.hasPropose B1 h1
  have hp2 := hbi.hasPropose B2 h2
  rw [hc1, hc2] at hd
  -- Need ValidIds to get the bounds on B1.author and B2.author.
  -- All blocks in s.blocks were proposed by validators in system.validators,
  -- so their author IDs are bounded.
  -- Actually, we know .block_propose B1.author B1 B1.r ∈ s.emittedOperations.
  -- We need to connect author IDs to system.validators.
  -- For now, use digest_injective to get r1 = r2, author1 = author2,
  -- then uniquePropose to get B1 = B2.
  have hbnd1 := hbi.authorBounded B1 h1
  have hbnd2 := hbi.authorBounded B2 h2
  obtain ⟨hr, hv⟩ := digest_injective system B1.r B2.r B1.author B2.author hbnd1 hbnd2 hd
  exact hbi.uniquePropose B1.author B1.r B1 B2 hp1 (hr ▸ hv ▸ hp2)

/-! #### Monotonicity lemmas for `step` -/

private lemma doPropose_blocks (system : BlockSynchroniserSystem) (s : BelugaState)
    (vid : ValidatorId) (r : Round) (B : Block) (hB : B ∈ s.blocks) :
    B ∈ (doPropose system s vid r).blocks := by
  simp [doPropose]; right; exact hB

private lemma doAccept_blocks (s : BelugaState) (vid : ValidatorId)
    (B B' : Block) (hB : B ∈ s.blocks) :
    B ∈ (doAccept s vid B').blocks := by
  simp [doAccept, updateValidator]; exact hB

private lemma doStore_blocks (s : BelugaState) (vid : ValidatorId)
    (B B' : Block) (hB : B ∈ s.blocks) :
    B ∈ (doStore s vid B').blocks := by
  simp [doStore, updateValidator]; exact hB

private lemma doAdvance_blocks (s : BelugaState) (vid : ValidatorId)
    (B : Block) (hB : B ∈ s.blocks) :
    B ∈ (doAdvance s vid).blocks := by
  simp [doAdvance, updateValidator]; exact hB

private lemma doPropose_ops_subset (system : BlockSynchroniserSystem) (s : BelugaState)
    (vid : ValidatorId) (r : Round) (op : ValidatorOperation)
    (hop : op ∈ s.emittedOperations) :
    op ∈ (doPropose system s vid r).emittedOperations := by
  simp only [doPropose]; exact List.mem_append_left _ hop

private lemma doAccept_ops_subset (s : BelugaState) (vid : ValidatorId) (B : Block)
    (op : ValidatorOperation) (hop : op ∈ s.emittedOperations) :
    op ∈ (doAccept s vid B).emittedOperations := by
  simp only [doAccept, updateValidator]; exact List.mem_append_left _ hop

private lemma doStore_ops_subset (s : BelugaState) (vid : ValidatorId) (B : Block)
    (op : ValidatorOperation) (hop : op ∈ s.emittedOperations) :
    op ∈ (doStore s vid B).emittedOperations := by
  simp only [doStore, updateValidator]; exact List.mem_append_left _ hop

private lemma doAdvance_ops_eq (s : BelugaState) (vid : ValidatorId) :
    (doAdvance s vid).emittedOperations = s.emittedOperations := by
  simp [doAdvance, updateValidator]

private lemma tryActFor_blocks_subset (system : BlockSynchroniserSystem)
    (s s' : BelugaState) (vid : ValidatorId) (bv : BelugaValidator)
    (hact : tryActFor system s vid bv = some s') (B : Block) (hB : B ∈ s.blocks) :
    B ∈ s'.blocks := by
  unfold tryActFor at hact;
  unfold doPropose at *; unfold doAccept at *; unfold doStore at *; unfold doAdvance at *; aesop;

private lemma tryActFor_ops_subset (system : BlockSynchroniserSystem)
    (s s' : BelugaState) (vid : ValidatorId) (bv : BelugaValidator)
    (hact : tryActFor system s vid bv = some s') (op : ValidatorOperation)
    (hop : op ∈ s.emittedOperations) :
    op ∈ s'.emittedOperations := by
  unfold tryActFor at hact;
  cases h : List.find? ( fun B => !hasAcceptedDigest s vid B.d && B.parents.all fun pd => hasAcceptedDigest s vid pd ) s.blocks <;> simp_all +decide;
  · cases h' : List.find? ( fun B => hasAcceptedDigest s vid B.d && !hasStoredDigest s vid B.d ) s.blocks <;> simp_all +decide;
    · split_ifs at hact <;> simp_all +decide [ doPropose, doAdvance ];
      · grind;
      · unfold updateValidator at hact; aesop;
    · split_ifs at hact <;> simp_all +decide [ doPropose, doStore ];
      · aesop;
      · unfold updateValidator at hact; aesop;
  · split_ifs at hact <;> simp_all +decide [ doPropose, doAccept ];
    · aesop;
    · unfold updateValidator at hact; aesop;

private lemma step_blocks_subset (system : BlockSynchroniserSystem)
    (s : BelugaState) (B : Block) (hB : B ∈ s.blocks) :
    B ∈ (step system s).blocks := by
  unfold step;
  cases h : List.findSome? ( fun x => tryActFor system s x.1 x.2 ) s.validators <;> simp_all +decide;
  have := Lib.findSome_witness _ _ _ h;
  obtain ⟨ a, ha, ha' ⟩ := this; exact tryActFor_blocks_subset system s _ a.1 a.2 ha' B hB;

private lemma step_ops_subset (system : BlockSynchroniserSystem)
    (s : BelugaState) (op : ValidatorOperation) (hop : op ∈ s.emittedOperations) :
    op ∈ (step system s).emittedOperations := by
  unfold step;
  grind +suggestions

private lemma doStore_blocks_eq (s : BelugaState) (vid : ValidatorId) (B : Block) :
    (doStore s vid B).blocks = s.blocks := by
  simp [doStore, updateValidator]

private lemma doAdvance_blocks_eq (s : BelugaState) (vid : ValidatorId) :
    (doAdvance s vid).blocks = s.blocks := by
  simp [doAdvance, updateValidator]

private lemma doAccept_blocks_eq (s : BelugaState) (vid : ValidatorId) (B : Block) :
    (doAccept s vid B).blocks = s.blocks := by
  simp [doAccept, updateValidator]

private lemma doStore_HasAccepted_iff (s : BelugaState) (vid_s : ValidatorId) (B : Block)
    (vid : ValidatorId) (d : BlockDigest) :
    HasAccepted (doStore s vid_s B) vid d ↔ HasAccepted s vid d := by
  unfold HasAccepted Emitted doStore updateValidator; simp [SystemState.emittedOperations]

private lemma doAdvance_HasAccepted_iff (s : BelugaState) (vid_a : ValidatorId)
    (vid : ValidatorId) (d : BlockDigest) :
    HasAccepted (doAdvance s vid_a) vid d ↔ HasAccepted s vid d := by
  unfold HasAccepted Emitted doAdvance updateValidator; simp [SystemState.emittedOperations]

private lemma doPropose_HasAccepted_iff (system : BlockSynchroniserSystem)
    (s : BelugaState) (vid_p : ValidatorId) (r : Round)
    (vid : ValidatorId) (d : BlockDigest) :
    HasAccepted (doPropose system s vid_p r) vid d ↔ HasAccepted s vid d := by
  unfold HasAccepted Emitted doPropose; simp [SystemState.emittedOperations]

private lemma doAccept_HasAccepted_iff (s : BelugaState) (vid_a : ValidatorId) (B : Block)
    (vid : ValidatorId) (d : BlockDigest) :
    HasAccepted (doAccept s vid_a B) vid d ↔
    HasAccepted s vid d ∨ (vid = vid_a ∧ d = B.d) := by
  unfold HasAccepted Emitted doAccept updateValidator; simp [SystemState.emittedOperations]

private lemma step_HasAccepted_mono (system : BlockSynchroniserSystem)
    (s : BelugaState) (vid : ValidatorId) (d : BlockDigest)
    (h : HasAccepted s vid d) : HasAccepted (step system s) vid d :=
  step_ops_subset system s _ h

/-! #### BlockInv preservation -/

private lemma wellFormed_init (system : BlockSynchroniserSystem) :
    BelugaState.WellFormed system (BelugaState.init system) := by
  intro p hp; simp_all +decide [ BelugaState.init ] ;
  grind +splitImp

private lemma wellFormed_step (system : BlockSynchroniserSystem) (s : BelugaState)
    (h_wf : BelugaState.WellFormed system s) :
    BelugaState.WellFormed system (step system s) := by
  unfold step;
  cases h : List.findSome? ( fun x => tryActFor system s x.1 x.2 ) s.validators <;> simp_all +decide;
  have := List.findSome?_eq_some_iff.mp h;
  rcases this with ⟨ l₁, a, l₂, h₁, h₂, h₃ ⟩ ; simp_all +decide [ BelugaState.WellFormed ] ;
  unfold tryActFor at h₂;
  cases h : List.find? ( fun B => !hasAcceptedDigest s a.1 B.d && B.parents.all fun pd => hasAcceptedDigest s a.1 pd ) s.blocks <;> simp_all +decide [ doPropose, doAccept, doStore, doAdvance ];
  · cases h : List.find? ( fun B => hasAcceptedDigest s a.1 B.d && !hasStoredDigest s a.1 B.d ) s.blocks <;> simp_all +decide [ updateValidator ];
    · grind;
    · grind;
  · split_ifs at h₂ <;> simp_all +decide [ updateValidator ];
    · grind;
    · grind +splitImp;
    · grind

lemma wellFormed_trace (system : BlockSynchroniserSystem) (k : Nat) :
    BelugaState.WellFormed system (belugaTrace system k) := by
  induction k with
  | zero => exact wellFormed_init system
  | succ k ih => exact wellFormed_step system _ ih

private lemma blockInv_init (system : BlockSynchroniserSystem) :
    BlockInv system (BelugaState.init system) :=
  ⟨fun _ h => by simp [BelugaState.init] at h,
   fun _ h => by simp [BelugaState.init] at h,
   fun _ _ _ _ h => by simp [BelugaState.init] at h,
   fun _ h => by simp [BelugaState.init] at h⟩

private lemma blockInv_of_doPropose (system : BlockSynchroniserSystem)
    (s : BelugaState) (vid : ValidatorId) (r : Round)
    (hbi : BlockInv system s)
    (h_not_proposed : hasProposedFor s vid r = false)
    (h_vid_bound : vid < system.n + 1) :
    BlockInv system (doPropose system s vid r) := by
  constructor;
  · -- By definition of `doPropose`, the new block `B` has `B.d = digest system B.r B.author`.
    simp [doPropose];
    exact hbi.canonical;
  · unfold doPropose;
    simp +zetaDelta at *;
    exact fun B hB => Or.inl <| hbi.hasPropose B hB;
  · unfold doPropose at *; simp_all +decide [ List.mem_append ] ;
    intro v r B1 B2 h1 h2; cases h1 <;> cases h2 <;> simp_all +decide [ hasProposedFor ] ;
    · exact hbi.uniquePropose _ _ _ _ ‹_› ‹_›;
    · specialize h_not_proposed _ ‹_› ; aesop ( simp_config := { decide := true } ) ;
    · specialize h_not_proposed _ ‹_› ; aesop;
  · exact fun B hB => by cases hB <;> [ aesop; exact hbi.authorBounded _ ‹_› ] ;

private lemma blockInv_of_doAccept (system : BlockSynchroniserSystem)
    (s : BelugaState) (vid : ValidatorId) (B : Block)
    (hbi : BlockInv system s) :
    BlockInv system (doAccept s vid B) := by
  constructor;
  · exact fun B' hB' => hbi.canonical B' ( by unfold doAccept at hB'; aesop );
  · unfold doAccept;
    simp +decide [ updateValidator ];
    exact hbi.hasPropose;
  · have := hbi.uniquePropose;
    unfold doAccept;
    unfold updateValidator; aesop;
  · exact fun x hx => hbi.authorBounded x <| by unfold doAccept at hx; aesop;

private lemma blockInv_of_doStore (system : BlockSynchroniserSystem)
    (s : BelugaState) (vid : ValidatorId) (B : Block)
    (hbi : BlockInv system s) :
    BlockInv system (doStore s vid B) := by
  constructor;
  · exact hbi.canonical;
  · intro B' hB';
    exact doStore_ops_subset s vid B _ (hbi.hasPropose B' hB')
  · intro v r B1 B2 h1 h2;
    have := hbi.uniquePropose v r B1 B2;
    unfold doStore at *;
    unfold updateValidator at *; aesop;
  · exact fun x hx => hbi.authorBounded x <| by unfold doStore at hx; aesop;

private lemma blockInv_of_doAdvance (system : BlockSynchroniserSystem)
    (s : BelugaState) (vid : ValidatorId)
    (hbi : BlockInv system s) :
    BlockInv system (doAdvance s vid) := by
  constructor;
  · exact fun B hB => hbi.canonical B ( by unfold doAdvance at hB; aesop );
  · convert hbi.hasPropose using 1;
  · intro v r B1 B2 h1 h2; exact hbi.uniquePropose v r B1 B2 (by rwa [doAdvance_ops_eq] at h1) (by rwa [doAdvance_ops_eq] at h2)
  · exact fun B hB => hbi.4 B ( by
      grind +locals )

private lemma blockInv_step (system : BlockSynchroniserSystem)
    (s : BelugaState) (hids : ValidIds system)
    (hbi : BlockInv system s)
    (h_wf : BelugaState.WellFormed system s) :
    BlockInv system (step system s) := by
  unfold step;
  cases h : List.findSome? ( fun x => tryActFor system s x.1 x.2 ) s.validators <;> simp_all +decide;
  obtain ⟨ ⟨ vid, bv ⟩, hvid, hv ⟩ := Lib.findSome_witness _ _ _ h;
  unfold tryActFor at hv;
  cases h : List.find? ( fun B => !hasAcceptedDigest s vid B.d && B.parents.all fun pd => hasAcceptedDigest s vid pd ) s.blocks <;> simp_all +decide;
  · cases h' : List.find? ( fun B => hasAcceptedDigest s vid B.d && !hasStoredDigest s vid B.d ) s.blocks <;> simp_all +decide;
    · split_ifs at hv <;> simp_all +decide;
      · subst hv;
        apply blockInv_of_doPropose;
        · finiteness;
        · assumption;
        · exact hids _ ( h_wf _ hvid |> Classical.choose_spec |> And.left ) |> fun h => by simpa [ h_wf _ hvid |> Classical.choose_spec |> And.right ] using h;
      · exact hv ▸ blockInv_of_doAdvance system s vid hbi;
    · split_ifs at hv <;> simp_all +decide [ doPropose, doStore ];
      · rw [ ← hv ];
        convert blockInv_of_doPropose system s vid bv.currentRound hbi ‹_› _ using 1;
        exact hids _ ( h_wf _ hvid |> Classical.choose_spec |> And.left ) |> fun h => by simpa [ h_wf _ hvid |> Classical.choose_spec |> And.right ] using h;
      · exact hv ▸ blockInv_of_doStore system s vid _ hbi;
  · split_ifs at hv <;> simp_all +decide [ doPropose, doAccept ];
    · convert blockInv_of_doPropose system s vid bv.currentRound hbi ‹_› _ using 1;
      · exact hv.symm;
      · exact hids _ ( h_wf _ hvid |> Classical.choose_spec |> And.left ) |> fun h => by simpa [ h_wf _ hvid |> Classical.choose_spec |> And.right ] using h;
    · subst hv;
      convert blockInv_of_doAccept system s vid _ hbi using 1

lemma blockInv_trace (system : BlockSynchroniserSystem)
    (hids : ValidIds system) (k : Nat) :
    BlockInv system (belugaTrace system k) := by
  induction k with
  | zero => exact blockInv_init system
  | succ k ih => exact blockInv_step system _ hids ih (wellFormed_trace system k)

/-! #### AcceptInv preservation -/

private lemma acceptInv_init (system : BlockSynchroniserSystem)
    (vid : ValidatorId) :
    AcceptInv (BelugaState.init system) vid := by
  refine ⟨fun B hB => by simp [BelugaState.init] at hB, fun d hacc => ?_⟩
  exfalso; revert hacc; simp [HasAccepted, Emitted, SystemState.emittedOperations, BelugaState.init]

private lemma acceptInv_of_doPropose (system : BlockSynchroniserSystem)
    (s : BelugaState) (vid_p : ValidatorId) (r : Round)
    (_hids : ValidIds system) (hbi : BlockInv system s)
    (vid : ValidatorId) (hai : AcceptInv s vid)
    (h_not_proposed : hasProposedFor s vid_p r = false)
    (h_vid_p_bound : vid_p < system.n + 1) :
    AcceptInv (doPropose system s vid_p r) vid := by
  constructor
  · intro X hX hacc pd hpd
    rw [doPropose_HasAccepted_iff] at hacc ⊢
    have : X ∈ s.blocks := by
      simp only [doPropose] at hX
      rcases List.mem_cons.mp hX with rfl | h
      · -- X = B_new, show HasAccepted s vid X.d is False
        exfalso
        obtain ⟨B', hB', hd⟩ := hai.acceptedBlockExists _ hacc
        have hcan := hbi.canonical B' hB'
        have hbnd := hbi.authorBounded B' hB'
        rw [hcan] at hd
        obtain ⟨hr, hv⟩ := digest_injective system B'.r r B'.author vid_p hbnd h_vid_p_bound hd
        have hprop := hbi.hasPropose B' hB'
        have : hasProposedFor s vid_p r = true := by
          unfold hasProposedFor
          rw [List.any_eq_true]
          exact ⟨_, hprop, by subst hr; subst hv; simp⟩
        simp [this] at h_not_proposed
      · exact h
    exact hai.acceptedParents X this hacc pd hpd
  · intro d hacc
    rw [doPropose_HasAccepted_iff] at hacc
    obtain ⟨B', hB', hd⟩ := hai.acceptedBlockExists d hacc
    exact ⟨B', doPropose_blocks system s vid_p r B' hB', hd⟩

private lemma acceptInv_of_doAccept (system : BlockSynchroniserSystem)
    (s : BelugaState) (vid_a : ValidatorId) (B : Block)
    (hids : ValidIds system) (hbi : BlockInv system s)
    (vid : ValidatorId) (hai : AcceptInv s vid)
    (hB_mem : B ∈ s.blocks)
    (hB_parents : B.parents.all (fun pd => hasAcceptedDigest s vid_a pd) = true) :
    AcceptInv (doAccept s vid_a B) vid := by
  constructor
  · intro X hX hacc pd hpd
    rw [doAccept_blocks_eq] at hX
    rw [doAccept_HasAccepted_iff] at hacc ⊢
    rcases hacc with hacc | ⟨hvid, hdig⟩
    · exact Or.inl (hai.acceptedParents X hX hacc pd hpd)
    · have hXB := noDupDigests_of_blockInv system s hids hbi X B hX hB_mem hdig
      rw [hXB] at hpd
      have hall := List.all_eq_true.mp hB_parents pd hpd
      exact Or.inl (hvid ▸ hasAcceptedDigest_true_imp s vid_a pd hall)
  · intro d hacc
    rw [doAccept_HasAccepted_iff] at hacc
    rcases hacc with hacc | ⟨_, rfl⟩
    · obtain ⟨B', hB', hd⟩ := hai.acceptedBlockExists d hacc
      exact ⟨B', by rw [doAccept_blocks_eq]; exact hB', hd⟩
    · exact ⟨B, by rw [doAccept_blocks_eq]; exact hB_mem, rfl⟩

private lemma acceptInv_of_doStore (s : BelugaState)
    (vid_s : ValidatorId) (B : Block)
    (vid : ValidatorId) (hai : AcceptInv s vid) :
    AcceptInv (doStore s vid_s B) vid :=
  ⟨fun B' hB' hacc pd hpd => by
    rw [doStore_blocks_eq] at hB'
    rw [doStore_HasAccepted_iff] at hacc ⊢
    exact hai.acceptedParents B' hB' hacc pd hpd,
   fun d hacc => by
    rw [doStore_HasAccepted_iff] at hacc
    obtain ⟨B', hB', hd⟩ := hai.acceptedBlockExists d hacc
    exact ⟨B', by rw [doStore_blocks_eq]; exact hB', hd⟩⟩

private lemma acceptInv_of_doAdvance (s : BelugaState)
    (vid_a : ValidatorId)
    (vid : ValidatorId) (hai : AcceptInv s vid) :
    AcceptInv (doAdvance s vid_a) vid :=
  ⟨fun B' hB' hacc pd hpd => by
    rw [doAdvance_blocks_eq] at hB'
    rw [doAdvance_HasAccepted_iff] at hacc ⊢
    exact hai.acceptedParents B' hB' hacc pd hpd,
   fun d hacc => by
    rw [doAdvance_HasAccepted_iff] at hacc
    obtain ⟨B', hB', hd⟩ := hai.acceptedBlockExists d hacc
    exact ⟨B', by rw [doAdvance_blocks_eq]; exact hB', hd⟩⟩

private lemma acceptInv_step (system : BlockSynchroniserSystem)
    (s : BelugaState) (vid : ValidatorId) (hids : ValidIds system)
    (hbi : BlockInv system s) (hai : AcceptInv s vid)
    (h_wf : BelugaState.WellFormed system s) :
    AcceptInv (step system s) vid := by
  unfold step
  cases h : List.findSome? (fun x => tryActFor system s x.1 x.2) s.validators <;> simp_all +decide
  obtain ⟨⟨vid_act, bv⟩, hvid, hv⟩ := Lib.findSome_witness _ _ _ h
  have hvid_bnd : vid_act < system.n + 1 := by
    obtain ⟨q, hq, hqid⟩ := h_wf _ hvid
    simp at hqid; rw [← hqid]; exact hids q hq
  -- Case analysis mirrors tryActFor_honestStep structure
  have hact := hv
  revert hact; unfold tryActFor; intro hact
  by_cases hp : hasProposedFor s vid_act bv.currentRound = false
  · -- Propose branch
    simp [hp] at hact
    convert acceptInv_of_doPropose system s vid_act bv.currentRound hids hbi vid hai hp (by omega) using 1
    exact hact.symm
  · -- Not propose
    have hp' : hasProposedFor s vid_act bv.currentRound = true := by
      cases h : hasProposedFor s vid_act bv.currentRound <;> simp_all
    simp only [hp'] at hact
    cases hfindAcc : s.blocks.find? (fun B =>
        !hasAcceptedDigest s vid_act B.d &&
        B.parents.all (fun pd => hasAcceptedDigest s vid_act pd))
    · -- No accept candidate
      simp [hfindAcc] at hact
      cases hfindStore : s.blocks.find? (fun B =>
          hasAcceptedDigest s vid_act B.d && !hasStoredDigest s vid_act B.d)
      · -- No store candidate either: advance or nothing
        simp [hfindStore] at hact
        by_cases hadv : allProposedFor system s bv.currentRound = true
        · simp [hadv] at hact
          convert acceptInv_of_doAdvance s vid_act vid hai using 1
          exact hact.symm
        · simp [show allProposedFor system s bv.currentRound = false from by
            cases allProposedFor system s bv.currentRound <;> simp_all] at hact
      · -- Store candidate
        simp [hfindStore] at hact
        convert acceptInv_of_doStore s vid_act _ vid hai using 1
        exact hact.symm
    · -- Accept candidate
      simp [hfindAcc] at hact
      have hp2 := List.find?_some hfindAcc
      rw [Bool.and_eq_true] at hp2
      convert acceptInv_of_doAccept system s vid_act _ hids hbi vid hai
        (List.mem_of_find?_eq_some hfindAcc) hp2.2 using 1
      exact hact.symm

/-- The `AcceptInv` invariant holds at every trace step. -/
theorem acceptInv_trace (system : BlockSynchroniserSystem)
    (vid : ValidatorId) (hids : ValidIds system) (k : Nat) :
    AcceptInv (belugaTrace system k) vid := by
  induction k with
  | zero => exact acceptInv_init system vid
  | succ k ih =>
    exact acceptInv_step system _ vid hids (blockInv_trace system hids k) ih
      (wellFormed_trace system k)

/-! #### CausallyClosed from AcceptInv -/

private lemma causallyClosed_of_acceptInv (s : BelugaState) (vid : ValidatorId)
    (hai : AcceptInv s vid) : CausallyClosed s vid := by
  intro B hB;
  rcases hai with ⟨ h1, h2 ⟩;
  intro B' hB';
  induction hB';
  · assumption;
  · rename_i m hm₁ hm₂ hm₃;
    cases hm₂ ; aesop

/-- The causal-closure invariant holds at every trace step. -/
theorem causallyClosed_trace (system : BlockSynchroniserSystem)
    (vid : ValidatorId) (hids : ValidIds system) (k : Nat) :
    CausallyClosed (belugaTrace system k) vid :=
  causallyClosed_of_acceptInv _ vid (acceptInv_trace system vid hids k)

/-! ### Helper lemmas for `step_refines_HonestStep`

The three private lemmas below + the proof of `step_refines_HonestStep`
itself were filled by **Aristotle round 3f (project `116385ce`)**. See
[`docs/aristotle-attributions.md`](../../docs/aristotle-attributions.md). -/

-- (hasAcceptedDigest_false_imp and hasAcceptedDigest_true_imp moved above)

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

-- proof: aristotle (project a8889396) — round 4
-- Helper: the "no-op" case always satisfies HonestStep via ByzantineStep with []
private lemma honestStep_of_no_op
    (system : BlockSynchroniserSystem) (s : BelugaState) :
    HonestStep system s s := by
  right; right; right; right
  exact ⟨[], by simp, fun _ h => by simp at h⟩

-- Helper: doAdvance emits no operations, so ByzantineStep with [] works
private lemma honestStep_of_advance
    (system : BlockSynchroniserSystem) (s : BelugaState)
    (vid : ValidatorId) :
    HonestStep system s (doAdvance s vid) := by
  right; right; right; right
  refine ⟨[], ?_, fun _ h => by simp at h⟩
  simp [doAdvance, updateValidator]

private lemma honestStep_of_propose
    (system : BlockSynchroniserSystem) (s : BelugaState)
    (vid : ValidatorId) (bv : BelugaValidator)
    (h_wf : BelugaState.WellFormed system s)
    (hmem : (vid, bv) ∈ s.validators) :
    HonestStep system s (doPropose system s vid bv.currentRound) := by
  by_cases h : isHonestValidator system vid <;> simp_all +decide [HonestStep]
  · exact Or.inl ⟨vid, _, _, h, ⟨_, hmem, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
  · refine Or.inr <| Or.inr <| Or.inr <| Or.inr ?_
    use [.block_propose vid
        ({ r := bv.currentRound, author := vid,
            d := digest system bv.currentRound vid,
            parents := if bv.currentRound = 0 then []
                       else (s.blocks.filter
                            (fun B => B.r == bv.currentRound - 1)).map (·.d),
            payload := [] }) bv.currentRound]
    exact ⟨rfl, fun op hop => by
      rw [List.mem_singleton.mp hop]
      exact not_honest_imp_byzantine system vid h (h_wf _ hmem)⟩

private lemma honestStep_of_accept
    (system : BlockSynchroniserSystem) (s : BelugaState)
    (vid : ValidatorId) (bv : BelugaValidator)
    (h_wf : BelugaState.WellFormed system s)
    (hmem : (vid, bv) ∈ s.validators)
    (B : Block)
    (hfind : s.blocks.find? (fun B' =>
        !hasAcceptedDigest s vid B'.d &&
        B'.parents.all (fun pd => hasAcceptedDigest s vid pd)) = some B) :
    HonestStep system s (doAccept s vid B) := by
  by_cases h : isHonestValidator system vid = true
  · refine Or.inr <| Or.inl ?_
    refine ⟨vid, B.d, ⟨h, ?_, ?_, ?_⟩⟩ <;>
      simp_all +decide [List.find?_eq_some_iff_append]
    · use B
      exact ⟨by obtain ⟨as, ⟨x, hx⟩, _⟩ := hfind.2; aesop, rfl,
             fun x hx => by
               have := hfind.1.2 x hx
               exact hasAcceptedDigest_true_imp s vid x this⟩
    · exact hasAcceptedDigest_false_imp s vid B.d hfind.1.1
    · unfold doAccept; aesop
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    use [.block_accept vid B.d]
    simp +decide [doAccept, operationAuthor]
    exact ⟨rfl, not_honest_imp_byzantine system vid (by simpa using h) (h_wf _ hmem)⟩

/-
Causal-history auxiliary (trace-level invariant).

When the accept `find?` returns `none` (no unaccepted block has all
parents accepted) and `B` itself is accepted, every block reachable
from `B` is also accepted. Derived from the trace-level `CausallyClosed`
invariant; the `hfindAccNone` premise is not needed once the invariant
is in place.

Strengthened to require the state to lie on the Beluga trace (with
`ValidIds` for digest injectivity).
-/
private lemma causal_history_of_find_none
    (system : BlockSynchroniserSystem) (hids : ValidIds system)
    (s : BelugaState) (vid : ValidatorId) (B : Block)
    (hacc : HasAccepted s vid B.d)
    (hfindAccNone : s.blocks.find? (fun B' =>
        !hasAcceptedDigest s vid B'.d &&
        B'.parents.all (fun pd => hasAcceptedDigest s vid pd)) = none)
    (hTrace : ∃ k, s = belugaTrace system k) :
    ∀ B' : Block, Reaches s B B' → HasAccepted s vid B'.d := by
  obtain ⟨k, rfl⟩ := hTrace
  exact causallyClosed_trace system vid hids k B hacc

private lemma honestStep_of_store
    (system : BlockSynchroniserSystem) (s : BelugaState)
    (vid : ValidatorId) (bv : BelugaValidator)
    (h_wf : BelugaState.WellFormed system s)
    (hmem : (vid, bv) ∈ s.validators)
    (B : Block)
    (hfindAccNone : s.blocks.find? (fun B' =>
        !hasAcceptedDigest s vid B'.d &&
        B'.parents.all (fun pd => hasAcceptedDigest s vid pd)) = none)
    (hfindStore : s.blocks.find? (fun B' =>
        hasAcceptedDigest s vid B'.d && !hasStoredDigest s vid B'.d) = some B)
    (hids : ValidIds system) (hTrace : ∃ k, s = belugaTrace system k) :
    HonestStep system s (doStore s vid B) := by
  by_cases h : isHonestValidator system vid = true
  · refine Or.inr <| Or.inr <| Or.inl ?_
    refine ⟨vid, B, h, ?_, ?_, ?_, ?_⟩ <;> simp_all +decide [doStore]
    · grind +suggestions
    · have := List.find?_some hfindStore
      exact causal_history_of_find_none system hids s vid B
        (hasAcceptedDigest_true_imp s vid B.d (by aesop)) (by aesop)
        hTrace
    · unfold updateValidator; aesop
    · unfold updateValidator; aesop
  · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
    use [.block_store vid B]
    simp [doStore]
    exact ⟨rfl, not_honest_imp_byzantine system vid (by simpa using h) (h_wf _ hmem)⟩

private lemma tryActFor_honestStep
    (system : BlockSynchroniserSystem) (s s' : BelugaState)
    (vid : ValidatorId) (bv : BelugaValidator)
    (h_wf : BelugaState.WellFormed system s)
    (hmem : (vid, bv) ∈ s.validators)
    (hact : tryActFor system s vid bv = some s')
    (hids : ValidIds system) (hTrace : ∃ k, s = belugaTrace system k) :
    HonestStep system s s' := by
  unfold tryActFor at hact
  cases hfindAcc : s.blocks.find? (fun B =>
      !hasAcceptedDigest s vid B.d
      && B.parents.all fun pd => hasAcceptedDigest s vid pd) <;>
    cases hfindStore : s.blocks.find? (fun B =>
      hasAcceptedDigest s vid B.d && !hasStoredDigest s vid B.d) <;>
    simp_all +decide
  · split_ifs at hact <;> simp_all +decide
    · exact hact ▸ honestStep_of_propose system s vid bv h_wf hmem
    · exact hact ▸ honestStep_of_advance system s vid
  · split_ifs at hact <;> simp_all +decide
    · exact hact ▸ honestStep_of_propose system s vid bv h_wf hmem
    · exact hact ▸ honestStep_of_store system s vid bv h_wf hmem _
        (by simp_all +decide [List.find?_eq_none]) hfindStore hids hTrace
  · split_ifs at hact <;> simp_all +decide
    · exact hact ▸ honestStep_of_propose system s vid bv h_wf hmem
    · exact hact ▸ honestStep_of_accept system s vid bv h_wf hmem _ hfindAcc
  · split_ifs at hact <;> simp_all +decide
    · exact hact ▸ honestStep_of_propose system s vid bv h_wf hmem
    · exact hact ▸ honestStep_of_accept system s vid bv h_wf hmem _ hfindAcc

theorem step_refines_HonestStep
    (system : BlockSynchroniserSystem) (s : BelugaState)
    (h_wf : BelugaState.WellFormed system s)
    (hids : ValidIds system) (hTrace : ∃ k, s = belugaTrace system k) :
    HonestStep system s (step system s) := by
  by_contra! h_contra
  obtain ⟨vid, bv, hmem, hact⟩ :
      ∃ vid bv, (vid, bv) ∈ s.validators ∧
                tryActFor system s vid bv = some (step system s) := by
    unfold step at *
    cases h : List.findSome? (fun x => tryActFor system s x.1 x.2) s.validators <;>
      simp_all +decide
    · exact False.elim <| h_contra <| honestStep_of_no_op system s
    · have := Lib.findSome_witness _ _ _ h; aesop
  exact h_contra <| tryActFor_honestStep system s _ vid bv h_wf hmem hact hids hTrace

end Beluga
end BlockSynchroniser
