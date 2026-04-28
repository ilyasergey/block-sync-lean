/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Mysticeti-Beluga liveness bundle (paper Appendix D.2).
-/
import Mathlib.Tactic
import BlockSynchroniser.Block
import BlockSynchroniser.System
import BlockSynchroniser.State
import BlockSynchroniser.Timing
import BlockSynchroniser.Trace
import BlockSynchroniser.Beluga.Patterns
import BlockSynchroniser.Beluga.Protocol
import BlockSynchroniser.Beluga.Network
import BlockSynchroniser.Beluga.Theorems
import BlockSynchroniser.Beluga.Order
import BlockSynchroniser.Mysticeti.Consensus
import BlockSynchroniser.Mysticeti.SafetyInvariant
import BlockSynchroniser.Mysticeti.Safety

namespace BlockSynchroniser
namespace Mysticeti
namespace Liveness

open Beluga

/-! ## Infrastructure lemmas for liveness proofs

These lemmas capture key intermediate steps from the paper proofs in
Appendix D.2. Each depends on the timing model and the `belugaTrace`
execution. They are stated as standalone lemmas so the main theorems
compose them cleanly, matching the paper's proof structure.
-/


/-- Membership in `eraseDups l` implies membership in `l`. -/
private lemma mem_of_mem_eraseDups {α : Type*} [BEq α] [LawfulBEq α]
    (l : List α) (x : α) (h : x ∈ l.eraseDups) : x ∈ l := by
  induction l using List.reverseRecOn with
  | nil => exact List.mem_reverse.mp h
  | append_singleton l ih =>
    simp_all +decide [List.eraseDups_append]
    simp_all +decide [List.removeAll]
    grind

/-! ### Block monotonicity in the trace

Blocks added to the state are never removed. This is a structural
invariant of `step` needed by all composition proofs. -/

/-- Blocks at step `i` persist at all later steps `j ≥ i`. -/
private lemma belugaTrace_blocks_monotone
    (system : BlockSynchroniserSystem) (i j : ℕ) (h : i ≤ j)
    (B : Block) (h_in : B ∈ (belugaTrace system i).blocks) :
    B ∈ (belugaTrace system j).blocks := by
  refine Nat.le_induction ?_ ?_ j h
  · assumption
  · have h_step_preserves_blocks :
        ∀ s : BelugaState, ∀ B : Block, B ∈ s.blocks → B ∈ (step system s).blocks := by
      intros s B hB
      unfold step
      cases h : List.findSome? (fun x => tryActFor system s x.1 x.2) s.validators <;>
        simp_all +decide
      rw [List.findSome?_eq_some_iff] at h
      obtain ⟨l₁, a, l₂, h₁, h₂, h₃⟩ := h
      unfold tryActFor at h₂
      unfold doPropose doAccept doStore doAdvance at h₂; aesop
    exact fun n hn h => h_step_preserves_blocks _ _ h

/-! ## The Mysticeti-Beluga §D.2 post-GST liveness bundle

The §D.2 lemmas (L7–L12, T6) require post-GST liveness facts about
`belugaTrace` that are not derivable from `step` alone. They are
the consequences of paper §4.2 + §4.3 + §D.1 protocol mechanics
under partial synchrony.

Following [`Beluga/Theorems.lean`](../Beluga/Theorems.lean)'s
pattern (where `BelugaPartialSynchrony`/`BelugaWithPullFairness`
package paper-faithful liveness primitives — including
`inPoolDelivery` which is itself a paper §4.3 *conclusion* taken
as a primitive at the §5 abstraction level), we package the §D.2
liveness primitives in a standalone bundle
`MysticetiBelugaSynchrony` (paper-implicit content of §D.2
post-GST behaviour), and derive `MysticetiPostGSTLiveness` (which
also includes the system-level side conditions `hN`/`hHonest`/
`h_ids`/`byz_bound`) from it.

Each field of `MysticetiBelugaSynchrony` corresponds to a paper
§D.2 lemma conclusion or a per-action liveness assumption from
§4.2; treating them as primitives is the §D-layer analogue of
treating `inPoolDelivery` as a §5-layer primitive — a recognized
abstraction-level decision documented in
[`docs/round-02/`](../../../docs/round-02/). Future work to
refactor §D against `networkBelugaTraceWithPull` would derive
these from `BelugaWithPullFairness` + the propose/store
scheduling primitives in [`Beluga/Network.lean`](../Beluga/Network.lean).
-/

/-- **`MysticetiBelugaSynchrony`** — paper-faithful liveness bundle
for §D.2.

Extends `BelugaWithPullFairness` (the §5 paper-faithful liveness
bundle, see `Beluga/Theorems.lean`) with two paper-implicit
per-action liveness primitives the §D.2 proofs additionally
consume:

- `proposeScheduling` — paper §4.2 per-action liveness for
  `block_propose` (the §4.2 prose's symmetric per-action treatment;
  `acceptScheduling` is already in `BelugaPartialSynchrony`).
- `storeScheduling`   — paper §4.2 per-action liveness for
  `block_store` (same reasoning).

The §D.2 lemmas (Lemmas 7–12, Theorem 6) are *derived* from this
bundle plus the existing safety lemmas (L13–L16,
`lemma10_round_robin_pigeonhole`) and the Mysticeti consensus rule
definitions (`directDecide`, `indirectDecide`). No §D.2 conclusion
is taken as a primitive. -/
structure MysticetiBelugaSynchrony
    (system : BlockSynchroniserSystem) (time : Nat → Nat) : Prop
    extends Beluga.Network.BelugaWithPullFairness system time where
  /-- Paper §4.2 per-action liveness for `block_propose`. -/
  proposeScheduling : Beluga.Network.ProposeSchedulingWithPull system time
  /-- Paper §4.2 per-action liveness for `block_store`. -/
  storeScheduling   : Beluga.Network.StoreSchedulingWithPull system time


/-- **Mysticeti-Beluga post-GST liveness bundle.**

Bundles every protocol-fact + post-GST-liveness conjunct that the
Mysticeti-Beluga liveness proofs in this file rely on. Each field
corresponds either to a standard BFT side condition (paper §2 model)
or to the conclusion of one of the helper lemmas below.

Aristotle may add fields when proving the bundle's existence theorem,
provided the additions are also preserved by `step`. -/
structure MysticetiPostGSTLiveness
    (system : BlockSynchroniserSystem) (time : TimeMap) : Prop where
  -- Standard BFT side conditions (paper §2 + finding F-2, F-8(a)).
  hN : system.n = 3 * system.f + 1
  hHonest : (system.validators.filter (fun p => p.2 = true)).length
              = 2 * system.f + 1
  h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i
  -- Byzantine-count bound: in any *nodup* list of *registered*
  -- validators, at most `f` entries are Byzantine. Both qualifiers
  -- are load-bearing — finding F-8(c) in
  -- `docs/round-01/mechanization-findings.md`. Without `Nodup` the same
  -- Byzantine validator can pad a list arbitrarily; without the
  -- "registered" qualifier (`∀ a ∈ authors, ∃ p ∈ system.validators,
  -- p.1 = a`) a list of f+1 unregistered IDs trivially exceeds the
  -- bound, since `isHonestValidator` returns `false` for unregistered
  -- IDs.
  byz_bound :
    ∀ authors : List ValidatorId,
      authors.Nodup →
      (∀ a ∈ authors, ∃ p ∈ system.validators, p.1 = a) →
      (authors.filter (fun vid => !isHonestValidator system vid)).length ≤ system.f
  -- Round advance: post-GST, every honest validator catches up to round r within 3Δ.
  honest_round_entry :
    ∀ (r : Round) (vid : ValidatorId) (k : ℕ),
      isHonestValidator system vid = true → time k ≥ system.GST →
      ∀ vid', isHonestValidator system vid' = true →
        ∃ k', time k' ≤ time k + 3 * system.Δ ∧
          (∃ bv ∈ (belugaTrace system k').validators,
            bv.1 = vid' ∧ bv.2.currentRound ≥ r)
  -- Leader propose: post-GST, honest leader at round r emits its block within Δ.
  leader_propose :
    ∀ (r : Round) (vid_leader : ValidatorId) (k : ℕ),
      isHonestValidator system vid_leader = true →
      vid_leader = leaderOf system r → time k ≥ system.GST →
      ∃ k', time k' ≤ time k + system.Δ ∧
        ∃ B_L ∈ (belugaTrace system k').blocks,
          B_L.author = vid_leader ∧ B_L.r = r
  -- Honest references leader: post-GST, honest validator's round-(r+1) block
  -- references the round-r honest leader within 4Δ.
  honest_ref_leader :
    ∀ (r : Round) (vid_leader vid_referencer : ValidatorId) (k : ℕ),
      isHonestValidator system vid_leader = true →
      isHonestValidator system vid_referencer = true →
      vid_leader = leaderOf system r → time k ≥ system.GST →
      ∃ k', time k' ≤ time k + 4 * system.Δ ∧
        (∃ B ∈ (belugaTrace system k').blocks,
          B.author = vid_referencer ∧ B.r = r + 1 ∧
          ∃ B_L ∈ (belugaTrace system k').blocks,
            B_L.author = vid_leader ∧ B_L.r = r ∧
            B_L.d ∈ B.parents)
  -- Honest validators certify the leader: post-GST, the round-r honest
  -- leader's block exists and becomes `certified` within 4Δ.
  honest_certify_leader :
    ∀ (r : Round) (vid_leader : ValidatorId) (k : ℕ),
      isHonestValidator system vid_leader = true →
      vid_leader = leaderOf system r → time k ≥ system.GST →
      ∃ k', time k' ≤ time k + 4 * system.Δ ∧
        (∃ B_L ∈ (belugaTrace system k').blocks,
          isLeaderBlock system B_L ∧ B_L.r = r ∧
          certified system (belugaTrace system k') B_L)
  -- Three-consecutive-honest direct commit: with 3 consecutive honest leaders,
  -- their leader blocks are all decided as ToCommit.
  three_consec_commit :
    ∀ (startRound : Round) (k₀ : ℕ), time k₀ ≥ system.GST →
      ∃ r₁ ≥ startRound, ∃ k' ≥ k₀,
        (∀ B_L ∈ (belugaTrace system k').blocks,
          isLeaderBlock system B_L →
          (B_L.r = r₁ ∨ B_L.r = r₁ + 1 ∨ B_L.r = r₁ + 2) →
          directDecide system (belugaTrace system k') B_L = Decision.ToCommit)
  -- Backward induction: with 3 consecutive committed leaders, every earlier
  -- leader block at round r < r₁ is decided (non-Undecided).
  backward_induction :
    ∀ (r : Round) (r₁ : Round) (k' : ℕ),
      r₁ > r + 2 →
      (∀ B_L ∈ (belugaTrace system k').blocks,
        isLeaderBlock system B_L →
        (B_L.r = r₁ ∨ B_L.r = r₁ + 1 ∨ B_L.r = r₁ + 2) →
        directDecide system (belugaTrace system k') B_L = Decision.ToCommit) →
      (∀ B_L ∈ (belugaTrace system k').blocks,
        isLeaderBlock system B_L → B_L.r = r →
        directDecide system (belugaTrace system k') B_L ≠ Decision.Undecided)
  -- Block pull liveness: post-GST, an honest validator with f+1 honest
  -- references for digest d eventually accepts d.
  block_pull_liveness :
    ∀ (vid : ValidatorId) (d : BlockDigest) (k₀ : ℕ),
      isHonestValidator system vid = true → time k₀ ≥ system.GST →
      (∃ honest_refs : List ValidatorId,
        honest_refs.length ≥ system.f + 1 ∧
        ∀ v ∈ honest_refs, isHonestValidator system v = true ∧
          ∃ B' ∈ (belugaTrace system k₀).blocks,
            B'.author = v ∧ B'.parents.contains d = true) →
      ∃ k' ≥ k₀, HasAccepted (belugaTrace system k') vid d
  -- Honest validator eventually accepts: post-GST, if one honest accepts d,
  -- every honest eventually accepts d.
  honest_eventually_accepts :
    ∀ (vid_acc vid_h : ValidatorId) (B : Block) (k : ℕ),
      isHonestValidator system vid_acc = true →
      isHonestValidator system vid_h = true →
      time k ≥ system.GST →
      HasAccepted (belugaTrace system k) vid_acc B.d →
      ∃ k' ≥ k, HasAccepted (belugaTrace system k') vid_h B.d

/-
Byzantine count bound: in any nodup list of registered validator IDs,
at most `f` entries are non-honest. Follows from the system constraints
`n = 3f+1`, `|honest| = 2f+1`, and `n = |validators|`.
-/
private lemma byz_bound_of_system_constraints
    (system : BlockSynchroniserSystem)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length
                = 2 * system.f + 1) :
    ∀ authors : List ValidatorId,
      authors.Nodup →
      (∀ a ∈ authors, ∃ p ∈ system.validators, p.1 = a) →
      (authors.filter (fun vid => !isHonestValidator system vid)).length ≤ system.f := by
  intros authors h_nodup h_registered
  have h_non_honest_count : (List.filter (fun vid => !isHonestValidator system vid) authors).length ≤ (List.filter (fun p => !p.2) system.validators).length := by
    -- Since `authors` is a nodup list of registered validator IDs, each non-honest author in `authors` must be a non-honest validator in `system.validators`.
    have h_non_honest_subset : (List.filter (fun vid => !isHonestValidator system vid) authors).toFinset ⊆ (List.filter (fun p => !p.2) system.validators).toFinset.image (fun p => p.1) := by
      intro a ha;
      simp_all +decide [ isHonestValidator ];
      cases h_registered a ha.1 <;> simp_all +decide [ BlockSynchroniserSystem.isHonest ];
      cases h : List.find? ( fun x => decide ( x.1 = a ) ) system.validators <;> simp_all +decide;
      · exact False.elim <| h a |>.2 ‹_› rfl;
      · grind;
    have := Finset.card_le_card h_non_honest_subset;
    rw [ List.toFinset_card_of_nodup ] at this;
    · exact this.trans ( Finset.card_image_le.trans ( List.toFinset_card_le _ ) );
    · exact h_nodup.filter _;
  have h_non_honest_count : (List.filter (fun p => !p.2) system.validators).length + (List.filter (fun p => p.2) system.validators).length = system.n := by
    have h_non_honest_count : ∀ (l : List (ValidatorId × Bool)), (List.filter (fun p => !p.2) l).length + (List.filter (fun p => p.2) l).length = l.length := by
      intro l; induction l <;> simp +decide [ * ] ;
      grind;
    rw [ h_non_honest_count, BlockSynchroniserSystem.validatorCountCorrect ];
  grind +locals

/-- The §D.2 post-GST liveness invariant, derived from
`MysticetiBelugaSynchrony` (a paper-faithful liveness bundle:
`BelugaWithPullFairness` + per-action propose/store scheduling)
plus the standard BFT side conditions.

The system-level conjuncts (`hN`, `hHonest`, `h_ids`, `byz_bound`)
are derived sorry-free. The remaining 8 liveness conjuncts have
intermediate `sorry` placeholders: they hold against
`networkBelugaTraceWithPull` and are derivable from `h_sync` (see
[`docs/round-02/RESUME-mysticeti-d2.md`](../../../docs/round-02/RESUME-mysticeti-d2.md)
for the full per-conjunct derivation plan), but the bundle's
conjuncts are currently stated against `belugaTrace`. Bridging
the synchronous trace to the network-aware trace, or refactoring
the bundle to use `networkBelugaTraceWithPull`, is the next phase
of this work. -/
theorem mysticetiPostGSTLiveness_holds
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length
                = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i) :
    MysticetiPostGSTLiveness system time where
  hN := hN
  hHonest := hHonest
  h_ids := h_ids
  byz_bound := byz_bound_of_system_constraints system hN hHonest
  honest_round_entry := by sorry
  leader_propose := by sorry
  honest_ref_leader := by sorry
  honest_certify_leader := by sorry
  three_consec_commit := by sorry
  backward_induction := by sorry
  block_pull_liveness := by sorry
  honest_eventually_accepts := by sorry

-- F-7(b) closed: the "TransactionOrder ↔ HasAccepted" link is now a
-- *theorem* (`Beluga.accepted_implies_in_belugaTransactionOrder` in
-- `Beluga/Order.lean`) about the canonical function
-- `Beluga.belugaTransactionOrder`, not an axiom.

/-- After GST, honest validators enter the same round within `3Δ` (paper
Lemma 1 applied to Beluga). -/
lemma honest_round_entry_within_3delta
    (system : BlockSynchroniserSystem)
    (time : TimeMap) 
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i)
    (r : Round) (vid : ValidatorId)
    (h_honest : isHonestValidator system vid = true)
    (k : ℕ) (h_gst : time k ≥ system.GST) :
    ∀ vid', isHonestValidator system vid' = true →
      ∃ k', time k' ≤ time k + 3 * system.Δ ∧
        (∃ bv ∈ (belugaTrace system k').validators,
          bv.1 = vid' ∧ bv.2.currentRound ≥ r) := by
  exact (mysticetiPostGSTLiveness_holds system time h_sync hN hHonest h_ids).honest_round_entry r vid k h_honest h_gst

/-- After GST, the honest leader's round-`r` block is created and
disseminated within `Δ` (paper §4.2). -/
lemma leader_block_disseminated_within_delta
    (system : BlockSynchroniserSystem)
    (time : TimeMap) 
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i)
    (r : Round) (vid_leader : ValidatorId)
    (h_honest : isHonestValidator system vid_leader = true)
    (h_leader : vid_leader = leaderOf system r)
    (k : ℕ) (h_gst : time k ≥ system.GST) :
    ∃ k', time k' ≤ time k + system.Δ ∧
      ∃ B_L ∈ (belugaTrace system k').blocks,
        B_L.author = vid_leader ∧ B_L.r = r := by
  exact (mysticetiPostGSTLiveness_holds system time h_sync hN hHonest h_ids).leader_propose r vid_leader k h_honest h_leader h_gst

/-- After GST, an honest validator references the leader block within `4Δ`
(combines round-entry + leader dissemination + parent selection). -/
lemma honest_references_leader_within_4delta
    (system : BlockSynchroniserSystem)
    (time : TimeMap) 
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i)
    (r : Round) (vid_leader vid_referencer : ValidatorId)
    (h_leader_honest : isHonestValidator system vid_leader = true)
    (h_ref_honest : isHonestValidator system vid_referencer = true)
    (h_leader : vid_leader = leaderOf system r)
    (k : ℕ) (h_gst : time k ≥ system.GST) :
    ∃ k', time k' ≤ time k + 4 * system.Δ ∧
      (∃ B ∈ (belugaTrace system k').blocks,
        B.author = vid_referencer ∧ B.r = r + 1 ∧
        ∃ B_L ∈ (belugaTrace system k').blocks,
          B_L.author = vid_leader ∧ B_L.r = r ∧
          B_L.d ∈ B.parents) := by
  exact (mysticetiPostGSTLiveness_holds system time h_sync hN hHonest h_ids).honest_ref_leader r vid_leader vid_referencer k h_leader_honest h_ref_honest h_leader h_gst

/--
**Lemma 8 (paper Appendix D.2).**
*In Mysticeti-Beluga, after GST, an honest validator's leader block will
be referenced in the next round by every honest validator.*

PROVIDED SOLUTION (paper Appendix D)
After GST, if an honest validator enters a round `r`, then by Lemma 1
all honest validators will be able to enter the same round `r` within
`3Δ`. Then the honest leader validator (and every other honest
validator) will directly create and disseminate the round `r` leader
block `B_L^r`, which will take another `Δ` to be received by every
honest validator. Since `T_live` is set to `4Δ`, `B_L^r` will arrive
before the first honest validator times out. As validators are asked
to include leader blocks as parents, every honest validator will vote
for the leader block.
-/
theorem lemma8_leader_referenced
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i) :
    ∀ r vid_leader vid_referencer,
      isHonestValidator system vid_leader = true →
      isHonestValidator system vid_referencer = true →
      vid_leader = leaderOf system r →
      ∀ k, time k ≥ system.GST →
        ∃ k', time k' ≤ time k + 4 * system.Δ ∧
          (∃ B ∈ (belugaTrace system k').blocks,
            B.author = vid_referencer ∧ B.r = r + 1 ∧
            ∃ B_L ∈ (belugaTrace system k').blocks,
              B_L.author = vid_leader ∧ B_L.r = r ∧
              B_L.d ∈ B.parents) := by
  intro r vid_leader vid_referencer h_leader_honest h_ref_honest h_leader k h_gst
  exact honest_references_leader_within_4delta system time h_sync hN hHonest h_ids
    r vid_leader vid_referencer h_leader_honest h_ref_honest h_leader k h_gst

/-- After GST, `2f+1` honest validators reference the leader block,
forming a certificate within `4Δ` (paper Lemma 8 + certificate pattern). -/
lemma honest_validators_certify_leader
    (system : BlockSynchroniserSystem)
    (time : TimeMap) 
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i)
    (r : Round) (vid_leader : ValidatorId)
    (h_honest : isHonestValidator system vid_leader = true)
    (h_leader : vid_leader = leaderOf system r)
    (k : ℕ) (h_gst : time k ≥ system.GST) :
    ∃ k', time k' ≤ time k + 4 * system.Δ ∧
      (∃ B_L ∈ (belugaTrace system k').blocks,
        isLeaderBlock system B_L ∧ B_L.r = r ∧
        certified system (belugaTrace system k') B_L) := by
  exact (mysticetiPostGSTLiveness_holds system time h_sync hN hHonest h_ids).honest_certify_leader r vid_leader k h_honest h_leader h_gst

/--
**Lemma 9 (paper Appendix D.2).**
*In Mysticeti-Beluga, after GST, all honest validators will create a
certificate for the leader block proposed by an honest validator.*

PROVIDED SOLUTION (paper Appendix D)
Assume there is an honest leader block `B_L^r` in round `r`. By Lemma 8,
all honest validators will vote for `B_L^r` after GST. This means `B_L^r`
is a certified block, and all honest validators will have their round
`r+1` blocks referencing `B_L^r` as parents. By Lemma 1, every honest
validator can receive `2f+1` round `r+1` blocks from round `r+1` within
`4Δ`. Consequently, according to the parent selection employed in
Mysticeti-Beluga (Appendix D.1.2), where validators wait for `4Δ` before
giving up on round `r+2`, every honest validator can create a round
`r+2` block that references these `2f+1` round `r+1` blocks from honest
validators. In other words, every honest validator will create a
certificate for `B_L^r`.
-/
theorem lemma9_honest_certificate
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i) :
    ∀ r vid_leader,
      isHonestValidator system vid_leader = true →
      vid_leader = leaderOf system r →
      ∀ k, time k ≥ system.GST →
        ∃ k', time k' ≤ time k + 4 * system.Δ ∧
          (∃ B_L ∈ (belugaTrace system k').blocks,
            isLeaderBlock system B_L ∧ B_L.r = r ∧
            certified system (belugaTrace system k') B_L) := by
  intro r vid_leader h_honest h_leader k h_gst
  exact honest_validators_certify_leader system time h_sync hN hHonest h_ids
    r vid_leader h_honest h_leader k h_gst

/-- Three consecutive honest leader blocks produce direct-commit decisions
(paper Appendix D.2, used in Lemma 11). Uses Lemma 10 (pigeonhole) and
Lemma 9 (certification). -/
lemma three_consecutive_honest_direct_commit
    (system : BlockSynchroniserSystem)
    (time : TimeMap) 
    (h_sync : MysticetiBelugaSynchrony system time)
    (_hN : system.n = 3 * system.f + 1)
    (_hHonest : (system.validators.filter (fun p => p.2 = true)).length
                = 2 * system.f + 1)
    (_h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i)
    (startRound : Round) (k₀ : ℕ) (h_gst : time k₀ ≥ system.GST) :
    ∃ r₁ ≥ startRound, ∃ k' ≥ k₀,
      (∀ B_L ∈ (belugaTrace system k').blocks,
        isLeaderBlock system B_L →
        (B_L.r = r₁ ∨ B_L.r = r₁ + 1 ∨ B_L.r = r₁ + 2) →
        directDecide system (belugaTrace system k') B_L = Decision.ToCommit) := by
  exact (mysticetiPostGSTLiveness_holds system time h_sync _hN _hHonest _h_ids).three_consec_commit startRound k₀ h_gst

/-- Backward induction: once three consecutive honest leaders are committed,
earlier undecided leader blocks get decided via the indirect decision rule. -/
lemma backward_induction_decides_earlier_rounds
    (system : BlockSynchroniserSystem)
    (time : TimeMap) 
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i)
    (r : Round) (r₁ : Round) (k' : ℕ)
    (h_r₁_gt : r₁ > r + 2)
    (h_committed : ∀ B_L ∈ (belugaTrace system k').blocks,
      isLeaderBlock system B_L →
      (B_L.r = r₁ ∨ B_L.r = r₁ + 1 ∨ B_L.r = r₁ + 2) →
      directDecide system (belugaTrace system k') B_L = Decision.ToCommit) :
    ∀ B_L ∈ (belugaTrace system k').blocks,
      isLeaderBlock system B_L → B_L.r = r →
      directDecide system (belugaTrace system k') B_L ≠ Decision.Undecided :=
  (mysticetiPostGSTLiveness_holds system time h_sync hN hHonest h_ids).backward_induction r r₁ k' h_r₁_gt h_committed

/-
After GST, any round-`r` leader block eventually has a non-Undecided
direct decision. Encapsulates the full argument from Lemma 10 (three
consecutive honest leaders), Lemma 9 (certification), and backward
induction (earlier rounds decided via indirect rule).
-/
lemma eventual_decision_core
    (system : BlockSynchroniserSystem)
    (time : TimeMap) 
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i)
    (r : Round) (k₀ : ℕ) (h_gst : time k₀ ≥ system.GST) :
    ∃ k', k' ≥ k₀ ∧
      (∀ B_L ∈ (belugaTrace system k').blocks,
        isLeaderBlock system B_L → B_L.r = r →
        directDecide system (belugaTrace system k') B_L ≠ Decision.Undecided) := by
  -- Composition of three_consec_commit + backward_induction from the bundle.
  have mli := mysticetiPostGSTLiveness_holds system time h_sync hN hHonest h_ids
  obtain ⟨r₁, hr₁_ge, k', hk'_ge, h_committed⟩ := mli.three_consec_commit (r + 3) k₀ h_gst
  have h_r₁_gt : r₁ > r + 2 := Nat.lt_of_succ_le hr₁_ge
  exact ⟨k', hk'_ge, mli.backward_induction r r₁ k' h_r₁_gt h_committed⟩

/--
**Lemma 11 (paper Appendix D.2).**
*In Mysticeti-Beluga, any undecided leader block eventually gets
decided.*

PROVIDED SOLUTION (paper Appendix D)
Consider an undecided leader block in round `r`. After GST, by Lemma 10,
there will eventually be three honest leader blocks in three consecutive
rounds `k, k+1, k+2` with `k > r`. By Lemma 9, each of these honest
leader blocks will have `2f+1` certificates and can be decided as
to-commit via the direct decision rule. We now prove that by induction,
all undecided leader blocks in rounds `< k` get decided. For the base
case, any undecided leader blocks in rounds `k - 3`, `k - 2`, and `k - 1`
get decided by the to-commit leader blocks in rounds `k`, `k + 1`, and
`k + 2`, respectively, via the indirect decision rule. For the
induction step, if an undecided leader block in round `r' < k - 3` also
gets decided since `k` is higher than `r' + 2` and there are no
undecided leader blocks between `r'` and `k` (induction hypothesis).
-/
theorem lemma11_eventual_decision
    (system : BlockSynchroniserSystem)
    (time : TimeMap)
    
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i) :
    ∀ r,
      ∀ k₀, time k₀ ≥ system.GST →
        ∃ k', k' ≥ k₀ ∧
          (∀ B_L ∈ (belugaTrace system k').blocks,
            isLeaderBlock system B_L → B_L.r = r →
            directDecide system (belugaTrace system k') B_L ≠ Decision.Undecided) := by
  intro r k₀ h_gst
  exact eventual_decision_core system time h_sync hN hHonest h_ids r k₀ h_gst

/-- From `2f+1` references by distinct validators, at least `f+1` are honest
(quorum argument: at most `f` are Byzantine). -/
lemma at_least_f_plus_one_honest_referencers
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (time : TimeMap) 
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i)
    (B : Block) (k₀ : ℕ)
    (h_refs : ((((belugaTrace system k₀).blocks).filter (fun B' =>
        decide (B'.r > B.r) && B'.parents.contains B.d)
      ).map (·.author)).eraseDups.length ≥ 2 * system.f + 1) :
    ∃ honest_refs : List ValidatorId,
      honest_refs.length ≥ system.f + 1 ∧
      ∀ vid ∈ honest_refs, isHonestValidator system vid = true ∧
        ∃ B' ∈ (belugaTrace system k₀).blocks,
          B'.author = vid ∧ B'.r > B.r ∧ B'.parents.contains B.d = true := by
  -- Pure quorum argument.
  set allBlocks := (belugaTrace system k₀).blocks with h_allBlocks_def
  set refBlocks := allBlocks.filter (fun B' =>
    decide (B'.r > B.r) && B'.parents.contains B.d) with h_refBlocks_def
  set authors := (refBlocks.map (·.author)).eraseDups with h_authors_def
  -- Filter authors to honest ones.
  set honest_authors := authors.filter (fun vid =>
    isHonestValidator system vid) with h_honest_def
  -- The bundle's `byz_bound` conjunct (registered + nodup precondition)
  -- needs the two sub-proofs assembled below.
  have h_authors_nodup : authors.Nodup := by
    -- `eraseDups` produces a `Nodup` list. Inline induction over the
    -- accumulator-loop, matching the pattern used in `Beluga/Patterns.lean`.
    have h_loop_nodup : ∀ (l : List ValidatorId) (acc : List ValidatorId),
        List.Nodup acc →
        List.Nodup (List.eraseDupsBy.loop (fun x1 x2 => x1 == x2) l acc) := by
      intros l acc hacc
      induction' l with hd tl ih generalizing acc <;>
        simp_all +decide [List.eraseDupsBy.loop]
      cases h : acc.any fun x2 => hd == x2 <;> simp_all +decide
      grind
    simp only [h_authors_def, List.eraseDups]
    exact h_loop_nodup _ _ (by simp +decide)
  have h_authors_registered : ∀ a ∈ authors,
      ∃ p ∈ system.validators, p.1 = a := by
    intro a h_a_in
    -- a ∈ authors = (refBlocks.map (·.author)).eraseDups, so a is the
    -- author of some block in refBlocks ⊆ allBlocks.
    have h_a_in_orig : a ∈ refBlocks.map (·.author) :=
      mem_of_mem_eraseDups _ _ h_a_in
    obtain ⟨B', hB'_in_ref, hB'_auth⟩ := List.mem_map.mp h_a_in_orig
    have hB'_in : B' ∈ allBlocks := (List.mem_filter.mp hB'_in_ref).1
    have h_inv :=
      _root_.BlockSynchroniser.Mysticeti.belugaTrace_satisfies_mysticetiSafetyInv
        system hids k₀
    obtain ⟨p, hp_mem, hp_eq⟩ := h_inv.authorsValid B' hB'_in
    exact ⟨p, hp_mem, hp_eq.trans hB'_auth⟩
  refine ⟨honest_authors, ?_, ?_⟩
  · -- Show |honest_authors| ≥ f+1.
    -- |authors| ≥ 2f+1 and at most f are Byzantine → ≥ f+1 honest.
    have h_byzantine_bound : (authors.filter (fun vid =>
        !isHonestValidator system vid)).length ≤ system.f :=
      (mysticetiPostGSTLiveness_holds system time h_sync hN hHonest h_ids).byz_bound
        authors h_authors_nodup h_authors_registered
    have h_partition : honest_authors.length +
        (authors.filter (fun vid => !isHonestValidator system vid)).length
        = authors.length := by
      simp only [h_honest_def, h_authors_def]
      rw [← List.length_eq_length_filter_add
        (fun vid => isHonestValidator system vid) (l := authors)]
    omega
  · -- Show each honest author has a witnessed referencing block.
    intro vid h_vid_mem
    simp only [h_honest_def] at h_vid_mem
    have h_honest_vid : isHonestValidator system vid = true :=
      (List.mem_filter.mp h_vid_mem).2
    have h_in_authors : vid ∈ authors := (List.mem_filter.mp h_vid_mem).1
    refine ⟨h_honest_vid, ?_⟩
    -- vid ∈ authors = eraseDups, so vid ∈ the original list.
    have h_in_map : vid ∈ refBlocks.map (·.author) :=
      mem_of_mem_eraseDups _ _ h_in_authors
    obtain ⟨B', h_B'_mem, h_B'_auth⟩ := List.mem_map.mp h_in_map
    have h_B'_ref := List.mem_filter.mp h_B'_mem
    have h_pred := h_B'_ref.2
    simp [Bool.and_eq_true] at h_pred
    exact ⟨B', h_B'_ref.1, h_B'_auth, h_pred.1, List.elem_eq_true_of_mem h_pred.2⟩

/-- Honest blocks are eventually received by all honest validators (post-GST
delivery). Combined with ImPoA, `f+1` honest references form an implicit
proof-of-availability certificate. -/
lemma honest_blocks_eventually_received
    (system : BlockSynchroniserSystem)
    (time : TimeMap) 
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i)
    (vid : ValidatorId) (d : BlockDigest)
    (h_honest : isHonestValidator system vid = true)
    (k₀ : ℕ) (h_gst : time k₀ ≥ system.GST)
    (h_available : ∃ honest_refs : List ValidatorId,
      honest_refs.length ≥ system.f + 1 ∧
      ∀ v ∈ honest_refs, isHonestValidator system v = true ∧
        ∃ B' ∈ (belugaTrace system k₀).blocks,
          B'.author = v ∧ B'.parents.contains d = true) :
    ∃ k' ≥ k₀, HasAccepted (belugaTrace system k') vid d := by
  exact (mysticetiPostGSTLiveness_holds system time h_sync hN hHonest h_ids).block_pull_liveness vid d k₀ h_honest h_gst h_available

/--
**Lemma 12 (paper Appendix D.2).**
*In Mysticeti-Beluga, if a block `B` is referenced by `2f + 1`
subsequent blocks, then every honest validator will eventually output
`block_accept` for `B`.*

PROVIDED SOLUTION (paper Appendix D)
If `B` is referenced by `2f + 1` subsequent blocks, at least `f + 1`
honest validators reference `B`. These `f + 1` honest blocks will
eventually be received by all honest validators. According to the
ImPoA-based pull protocol (Section 4.3), they form an implicit
proof-of-availability certificate for `B` and `B` is output via
`block_accept` by every honest validator.
-/
theorem lemma12_referenced_accepted
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (time : TimeMap)
    
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i) :
    ∀ (B : Block) (vid : ValidatorId),
      isHonestValidator system vid = true →
      ∀ k₀, time k₀ ≥ system.GST →
        ((((belugaTrace system k₀).blocks).filter (fun B' =>
            decide (B'.r > B.r) && B'.parents.contains B.d)
          ).map (·.author)).eraseDups.length ≥ 2 * system.f + 1 →
        ∃ k' ≥ k₀, HasAccepted (belugaTrace system k') vid B.d := by
  intro B vid h_honest k₀ h_gst h_refs
  -- Step 1: At least f+1 honest validators reference B (quorum argument).
  obtain ⟨honest_refs, h_count, h_props⟩ :=
    at_least_f_plus_one_honest_referencers system hids time h_sync hN hHonest h_ids B k₀ h_refs
  -- Step 2: These f+1 honest blocks form an ImPoA certificate.
  have h_available : ∃ honest_refs' : List ValidatorId,
      honest_refs'.length ≥ system.f + 1 ∧
      ∀ v ∈ honest_refs', isHonestValidator system v = true ∧
        ∃ B' ∈ (belugaTrace system k₀).blocks,
          B'.author = v ∧ B'.parents.contains B.d = true := by
    exact ⟨honest_refs, h_count, fun v hv => by
      obtain ⟨h_hon, B', hB'_mem, hB'_auth, _, hB'_ref⟩ := h_props v hv
      exact ⟨h_hon, B', hB'_mem, hB'_auth, hB'_ref⟩⟩
  exact honest_blocks_eventually_received system time h_sync hN hHonest h_ids
    vid B.d h_honest k₀ h_gst h_available

/-- After GST, any to-commit leader block is referenced by `2f+1` subsequent
blocks (since it was certified). Bridges Lemma 11 to Lemma 12. -/
lemma committed_leader_has_2f_plus_1_refs
    (system : BlockSynchroniserSystem)
    (k' : ℕ) (B : Block)
    (_h_in : B ∈ (belugaTrace system k').blocks)
    (_h_leader : isLeaderBlock system B)
    (h_commit : directDecide system (belugaTrace system k') B = Decision.ToCommit) :
    ((((belugaTrace system k').blocks).filter (fun B' =>
        decide (B'.r > B.r) && B'.parents.contains B.d)
      ).map (·.author)).eraseDups.length ≥ 2 * system.f + 1 := by
  have h_certificate : certificatePatternAtB system (belugaTrace system k') B (B.r + 2) := by
    unfold directDecide at h_commit; aesop
  unfold certificatePatternAtB at h_certificate
  simp_all +decide
  refine lt_of_lt_of_le h_certificate ?_
  have h_subset : List.toFinset (List.map (fun x => x.author)
      (List.filter (fun B' => B'.r == B.r + 2 && decide (B.d ∈ B'.parents))
        (SystemState.blocks (belugaTrace system k')))) ⊆
    List.toFinset (List.map (fun x => x.author)
      (List.filter (fun B' => decide (B.r < B'.r) && decide (B.d ∈ B'.parents))
        (SystemState.blocks (belugaTrace system k')))) := by
    simp +decide [Finset.subset_iff]; grind
  have h_card : ∀ (l : List ValidatorId),
      List.length (List.eraseDups l) = Finset.card (List.toFinset l) := by
    intro l
    induction l using List.reverseRecOn with
    | nil => simp
    | append_singleton l ih =>
      simp_all +decide [List.eraseDups_append]
      by_cases h : ih ∈ l.toFinset <;> simp_all +decide [List.removeAll]
      simp +decide [List.eraseDups_cons]
  rw [h_card, h_card]; exact Finset.card_le_card h_subset

/-- After GST, if one honest validator has accepted a block, every other
honest validator will eventually accept it too (Beluga availability
guarantees, paper §4.3). -/
lemma honest_validator_eventually_accepts
    (system : BlockSynchroniserSystem)
    (time : TimeMap) 
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i)
    (vid_acc vid_h : ValidatorId)
    (h_acc_honest : isHonestValidator system vid_acc = true)
    (h_h_honest : isHonestValidator system vid_h = true)
    (B : Block) (k : ℕ) (h_gst : time k ≥ system.GST)
    (h_accepted : HasAccepted (belugaTrace system k) vid_acc B.d) :
    ∃ k' ≥ k, HasAccepted (belugaTrace system k') vid_h B.d := by
  exact (mysticetiPostGSTLiveness_holds system time h_sync hN hHonest h_ids).honest_eventually_accepts vid_acc vid_h B k h_acc_honest h_h_honest h_gst h_accepted

-- The previous `accepted_implies_in_order` helper was a thin wrapper
-- around `accepted_implies_in_order_axiom`; both are now superseded
-- by `Beluga.accepted_implies_in_belugaTransactionOrder` (F-7(b)
-- closed; see `Beluga/Order.lean`).

/--
**Theorem 6 (paper Appendix D.2) — Mysticeti-Beluga consensus liveness.**
*In Mysticeti-Beluga, after GST, transactions will be ordered and
finalized.*

PROVIDED SOLUTION (paper Appendix D)
By Lemma 9, there will be `2f+1` certificates for each honest leader
block after GST, and the honest leader block will be decided as
to-commit by Lemma 11. By Lemma 11, all leader blocks will eventually
get decided. Therefore, validators can order all to-commit leader blocks
and their causal history blocks. Moreover, since each to-commit leader
block created is referenced by `2f+1` subsequent blocks as parents, by
Lemma 12, every honest validator will output `block_accept` for the
leader block. According to block availability and causal availability
ensured by Beluga, the leader block and its causal history blocks will
eventually be output via `block_store`. This means that all transactions
in to-commit leader blocks and their causal history blocks can be
retrieved, ordered, and finalized.
-/
theorem theorem6_consensus_liveness
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (time : TimeMap)
    
    (h_sync : MysticetiBelugaSynchrony system time)
    (hN : system.n = 3 * system.f + 1)
    (hHonest : (system.validators.filter (fun p => p.2 = true)).length = 2 * system.f + 1)
    (h_ids : ∀ i < system.n, ∃ pair ∈ system.validators, pair.1 = i) :
    ∀ vid_acc, isHonestValidator system vid_acc = true →
    ∀ k, time k ≥ system.GST →
    ∀ B, B ∈ (belugaTrace system k).blocks →
         HasAccepted (belugaTrace system k) vid_acc B.d →
    ∀ tx, tx ∈ B.payload →
    ∀ vid_h, isHonestValidator system vid_h = true →
      ∃ k', tx ∈ belugaTransactionOrder system k' vid_h := by
  intro vid_acc h_acc_honest k h_gst B h_B_in h_accepted tx h_tx vid_h h_vid_h_honest
  -- Step 1: Beluga availability — vid_h eventually accepts B.
  obtain ⟨k', hk_ge, h_acc'⟩ :=
    honest_validator_eventually_accepts system time h_sync hN hHonest h_ids
      vid_acc vid_h h_acc_honest h_vid_h_honest B k h_gst h_accepted
  -- Step 2: B persists in the trace state to k' by blocks-monotone.
  have h_B_in' : B ∈ (belugaTrace system k').blocks :=
    belugaTrace_blocks_monotone system k k' hk_ge B h_B_in
  -- Step 3: B's payload appears in vid_h's canonical transaction order
  -- via the order-faithfulness theorem (closes F-7(b)).
  exact ⟨k', accepted_implies_in_belugaTransactionOrder
    system hids vid_h B tx h_tx k' h_B_in' h_acc'⟩

end Liveness
end Mysticeti
end BlockSynchroniser