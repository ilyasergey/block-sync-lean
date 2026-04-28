/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Canonical transaction order for the Beluga trace.

Closes finding F-7(b) (the order-from-view modeling artifact in
`docs/round-01/mechanization-findings.md`) by defining the transaction order as a
concrete *function* of trace state rather than an abstract parameter. The
order-faithfulness theorem `accepted_implies_in_belugaTransactionOrder` is then
a *theorem* about this function, not an axiom.

The order is the canonical traversal: walk the validator's `block_accept`
operations in the order they were emitted, look up the corresponding block in
the state, and concatenate payloads.

Depends only on the structural trace invariants `BlockInv` and
`digest_injective` from `Beluga/Protocol.lean` (already proved in project
`3f6cf619`). No fairness or liveness needed.
-/
import Mathlib.Tactic
import BlockSynchroniser.Block
import BlockSynchroniser.System
import BlockSynchroniser.State
import BlockSynchroniser.Operations
import BlockSynchroniser.Beluga.Protocol

namespace BlockSynchroniser
namespace Beluga

/-- State-level transaction order: walks an arbitrary `BelugaState`'s
emitted ops, picks up `block_accept v d` with `v = vid`, looks up
the block by digest, and concatenates payload. -/
def belugaTransactionOrderState
    (s : BelugaState) (vid : ValidatorId) : List Transaction :=
  s.emittedOperations.flatMap fun op =>
    match op with
    | .block_accept v d =>
      if v = vid then
        match getBlockByDigest s d with
        | some B => B.payload
        | none   => []
      else []
    | _ => []

/-- The canonical transaction order produced by an honest validator's
state at synchronous trace step `k`. -/
def belugaTransactionOrder
    (system : BlockSynchroniserSystem) (k : Nat) (vid : ValidatorId) : List Transaction :=
  belugaTransactionOrderState (belugaTrace system k) vid

/-- Block-by-digest uniqueness in the trace state: any two blocks in
`(belugaTrace system k).blocks` with the same digest are equal.

Derived from the structural invariant `BlockInv` (project `3f6cf619`).
-/
lemma block_unique_by_digest_in_trace
    (system : BlockSynchroniserSystem) (hids : ValidIds system)
    (k : Nat) (B B' : Block)
    (hB  : B  ∈ (belugaTrace system k).blocks)
    (hB' : B' ∈ (belugaTrace system k).blocks)
    (h_d : B.d = B'.d) :
    B = B' := by
  -- Trace invariant `BlockInv` says: every block has canonical digest
  -- determined by `(round, author)`, and `(author, round)` proposes are
  -- unique.
  have h_inv : BlockInv system (belugaTrace system k) := blockInv_trace system hids k
  -- digest injection (under ValidIds) gives r and author equality.
  have h_canon  : B.d  = digest system B.r  B.author  := h_inv.canonical _ hB
  have h_canon' : B'.d = digest system B'.r B'.author := h_inv.canonical _ hB'
  rw [h_canon, h_canon'] at h_d
  have hbA  : B.author  < system.n + 1 := h_inv.authorBounded _ hB
  have hbA' : B'.author < system.n + 1 := h_inv.authorBounded _ hB'
  obtain ⟨h_r, h_a⟩ := digest_injective system B.r B'.r B.author B'.author hbA hbA' h_d
  -- Same r, same author → unique propose op → same block.
  have hp  : ValidatorOperation.block_propose B.author  B  B.r  ∈ (belugaTrace system k).emittedOperations := h_inv.hasPropose B  hB
  have hp' : ValidatorOperation.block_propose B'.author B' B'.r ∈ (belugaTrace system k).emittedOperations := h_inv.hasPropose B' hB'
  rw [h_r, h_a] at hp
  exact h_inv.uniquePropose _ _ _ _ hp hp'

/-- **Order faithfulness theorem (closes F-7(b)).**

If an honest validator has accepted a block `B` that is in the trace
state at step `k`, then every transaction in `B.payload` appears in
that validator's canonical transaction order.

Pure structural derivation; depends only on `BlockInv` /
`digest_injective` / `getBlockByDigest`. -/
theorem accepted_implies_in_belugaTransactionOrder
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (vid_h : ValidatorId)
    (B : Block) (tx : Transaction) (h_tx : tx ∈ B.payload)
    (k : Nat)
    (h_in : B ∈ (belugaTrace system k).blocks)
    (h_accepted : HasAccepted (belugaTrace system k) vid_h B.d) :
    tx ∈ belugaTransactionOrder system k vid_h := by
  -- Step 1: HasAccepted unfolds to membership of the block_accept op.
  have h_op_mem : ValidatorOperation.block_accept vid_h B.d ∈
      (belugaTrace system k).emittedOperations := h_accepted
  -- Step 2: Show getBlockByDigest returns B (via block-unique-by-digest).
  have h_get : getBlockByDigest (belugaTrace system k) B.d = some B := by
    unfold getBlockByDigest
    rcases h_some : (belugaTrace system k).blocks.find?
        (fun b => decide (b.d = B.d)) with _ | B'
    · -- find? = none contradicts B ∈ blocks with B.d = B.d.
      exfalso
      have h_no_match : ∀ b ∈ (belugaTrace system k).blocks,
          ¬ decide (b.d = B.d) = true := List.find?_eq_none.mp h_some
      have := h_no_match B h_in
      simp at this
    · -- find? = some B'. The predicate at B' holds, so B'.d = B.d. By
      -- uniqueness, B' = B.
      have h_mem : B' ∈ (belugaTrace system k).blocks :=
        List.mem_of_find?_eq_some h_some
      have h_B'_d : B'.d = B.d := by
        have := List.find?_some h_some
        simpa using this
      have h_eq : B' = B :=
        block_unique_by_digest_in_trace system hids k B' B h_mem h_in h_B'_d
      subst h_eq; exact h_some
  -- Step 3: walk the flatMap. The block_accept op fires the branch.
  unfold belugaTransactionOrder belugaTransactionOrderState
  rw [List.mem_flatMap]
  refine ⟨.block_accept vid_h B.d, h_op_mem, ?_⟩
  simp only [h_get]
  exact h_tx

end Beluga
end BlockSynchroniser
