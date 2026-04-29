/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Mysticeti-Beluga safety bundle (paper Appendix D.3).
-/
import Mathlib.Tactic
import BlockSynchroniser.Block
import BlockSynchroniser.State
import BlockSynchroniser.System
import BlockSynchroniser.Causal
import BlockSynchroniser.Quorum
import BlockSynchroniser.Beluga.Patterns
import BlockSynchroniser.Beluga.AdmissionInvariant
import BlockSynchroniser.Mysticeti.SafetyInvariant
import BlockSynchroniser.Mysticeti.Consensus

set_option linter.unusedSimpArgs false

namespace BlockSynchroniser

/-- Transitivity of the `Reaches` relation: if `a` reaches `b` and `b`
reaches `c`, then `a` reaches `c`. -/
theorem Reaches.trans {S : Type} [SystemState S] {state : S} {a b c : Block}
    (hab : Reaches state a b) (hbc : Reaches state b c) : Reaches state a c := by
  induction hbc with
  | refl => exact hab
  | step _ h_parent ih => exact Reaches.step ih h_parent

namespace Mysticeti
namespace Safety

open Beluga

/-- `C` is a certificate for `B` if `C` is in round `B.r + 1`, references
`B` as a parent (so `B.d ∈ C.parents`), and both blocks are in the state.

Direct (round-`r+1`) certificate; the paper's broader notion includes
transitive references handled below via `Reaches`. -/
def isCertificateFor {S} [SystemState S] (state : S) (C B : Block) : Prop :=
  C.r = B.r + 1 ∧
  B.d ∈ C.parents ∧
  C ∈ SystemState.blocks state ∧
  B ∈ SystemState.blocks state

/-
In a list of ≥ f+1 registered validators, at least one is honest.
Follows from h_byz_bound: at most f validators are Byzantine, so a list
of > f registered validators contains at least one honest one.
-/
private lemma exists_honest_in_shared
    (system : BlockSynchroniserSystem)
    (shared : List ValidatorId)
    (h_shared_nodup : shared.Nodup)
    (h_shared_len : shared.length ≥ system.f + 1)
    (h_shared_valid : ∀ vid ∈ shared, ∃ pair ∈ system.validators, pair.1 = vid)
    (h_byz_bound : (system.validators.filter (fun p => p.2 = false)).length
      ≤ system.f) :
    ∃ v ∈ shared, isHonestValidator system v := by
  contrapose! h_byz_bound;
  refine' lt_of_lt_of_le h_shared_len _;
  have h_byzantine_count : List.toFinset (List.map (fun p => p.1) (List.filter (fun p => p.2 = false) system.validators)) ⊇ List.toFinset shared := by
    intro x hx; specialize h_byz_bound x; simp_all +decide [ isHonestValidator ] ;
    cases h_shared_valid x hx <;> simp_all +decide [ BlockSynchroniserSystem.isHonest ];
    cases h : List.find? ( fun x_1 => decide ( x_1.1 = x ) ) system.validators <;> simp_all +decide;
    · exact False.elim <| h x |>.2 ‹_› rfl;
    · grind;
  have := Finset.card_mono h_byzantine_count; simp_all +decide [ List.toFinset_card_of_nodup ] ;
  exact this.trans ( List.toFinset_card_le _ ) |> le_trans <| by simp +decide [ List.filter_eq ] ;

/--
**Lemma 12 (paper Appendix D.3).**

> *In Mysticeti-Beluga, if `2f + 1` round `r + 1` blocks from
> distinct validators are certificates of a block `B`, then every
> block in any round `r' > r` must (directly or transitively)
> reference a certificate for `B` formed in round `r`.*

**Note on indexing.** The paper writes "round `r` blocks ... are
certificates of a block `B`", but a *certificate for `B`* is a
block in round `B.r + 1` (it references `B` as a parent). So the
paper's "round `r`" in this lemma refers to *the certificate's
round*, i.e., `r = B.r + 1`. Our Lean statement makes this explicit:
`B` is the block being certified, the certificates are at
`C.r = B.r + 1`, and we conclude for every `B'` with
`B'.r > B.r + 1` that `B'` `Reaches` some certificate for `B`.

The two phrasings are equivalent — the paper's `r' > r` becomes our
`B'.r > B.r + 1` after the index shift.

Paper proof sketch: consider round `B.r + 2`. Every block in this
round references `2f + 1` blocks from round `B.r + 1`. By quorum
intersection, any such set intersects the `2f + 1` certificates of
`B` in at least one honest validator. Since honest validators do
not equivocate, every round `B.r + 2` block must reference a
certificate for `B`. Induction on rounds propagates to all
`r' > B.r + 1`.
-/
theorem lemma12_cert_persistence
    (system : BlockSynchroniserSystem) {S} [SystemState S] (state : S)
    (_h_no_eq : NoEquivocationInParents system state)
    (h_admission : AdmissionWellFormed system state)
    -- Standard BFT side conditions.
    (hN : system.n = 3 * system.f + 1)
    (h_authors_valid : ∀ B' ∈ SystemState.blocks state,
      ∃ pair ∈ system.validators, pair.1 = B'.author)
    (h_byz_bound : (system.validators.filter (fun p => p.2 = false)).length
      ≤ system.f)
    -- Honest validators produce at most one block per (author, round) pair.
    -- In a real protocol, this follows from digital signatures + honest behavior.
    (h_honest_unique : ∀ B₁ ∈ SystemState.blocks state, ∀ B₂ ∈ SystemState.blocks state,
      isHonestValidator system B₁.author →
      B₁.author = B₂.author → B₁.r = B₂.r → B₁ = B₂)
    (B : Block) (h_B : B ∈ SystemState.blocks state)
    (h_cert : ∃ certs : List Block,
                certs.length ≥ 2 * system.f + 1 ∧
                certs.Nodup ∧
                (certs.map (·.author)).Nodup ∧
                ∀ C ∈ certs, isCertificateFor state C B)
    (B' : Block) (h_in : B' ∈ SystemState.blocks state)
    (h_later : B'.r > B.r + 1) :
    ∃ C, isCertificateFor state C B ∧ Reaches state B' C := by
  -- The base case (round B.r + 2) is now derivable from
  -- `h_admission` + `h_cert` + `Quorum.quorumIntersection` +
  -- `h_no_eq` + `hN` (paper Appendix D's quorum-intersection step).
  -- The inductive step uses `h_admission` for the previous-round
  -- parent + IH + `Reaches.trans`.
  -- By induction on $d = B'.r - (B.r + 2)$, we can show that there exists a certificate for $B$ that $B'$ reaches.
  have h_ind : ∀ d ≥ 0, ∀ B' : Block, B' ∈ SystemState.blocks state → B'.r = B.r + 2 + d → ∃ C, isCertificateFor state C B ∧ Reaches state B' C := by
    intro d hd B' hB' hB'_r
    induction' d with d ih generalizing B';
    · obtain ⟨ certs, hcerts₁, hcerts₂, hcerts₃, hcerts₄ ⟩ := h_cert;
      obtain ⟨parents, hparents₁, hparents₂, hparents₃⟩ : ∃ parents : List Block, parents.length ≥ 2 * system.f + 1 ∧ (parents.map (·.author)).Nodup ∧ ∀ P ∈ parents, P ∈ SystemState.blocks state ∧ P.d ∈ B'.parents ∧ P.r + 1 = B'.r := by
        have := h_admission B' hB';
        grind;
      -- By quorum intersection, there exists a shared list of at least f+1 elements between parents and certs.
      obtain ⟨shared, hshared₁, hshared₂⟩ : ∃ shared : List ValidatorId, shared.Nodup ∧ shared.length ≥ system.f + 1 ∧ ∀ vid ∈ shared, vid ∈ parents.map (·.author) ∧ vid ∈ certs.map (·.author) := by
        apply Quorum.quorumIntersection system (parents.map (·.author)) (certs.map (·.author));
        · constructor;
          · assumption;
          · grind;
        · constructor;
          · assumption;
          · grind +locals;
        · exact hN;
      obtain ⟨v, hv⟩ : ∃ v ∈ shared, isHonestValidator system v := by
        apply exists_honest_in_shared;
        · assumption;
        · linarith;
        · grind;
        · exact h_byz_bound;
      obtain ⟨P, hP⟩ : ∃ P ∈ parents, P.author = v := by
        simpa using hshared₂.2 v hv.1 |>.1
      obtain ⟨C, hC⟩ : ∃ C ∈ certs, C.author = v := by
        simpa using hshared₂.2 v hv.1 |>.2;
      have hP_eq_C : P = C := by
        grind +locals;
      use C;
      exact ⟨ hcerts₄ C hC.1, Reaches.step ( Reaches.refl _ ) ⟨ by aesop, by aesop, by aesop ⟩ ⟩;
    · -- By the admission invariant, B' has parents with ≥ 2f+1 entries, each P at round B'.r - 1.
      obtain ⟨parents, h_parents⟩ : ∃ parents : List Block, parents.length ≥ 2 * system.f + 1 ∧ (parents.map (·.author)).Nodup ∧ ∀ P ∈ parents, P ∈ SystemState.blocks state ∧ P.d ∈ B'.parents ∧ P.r = B'.r - 1 := by
        have := h_admission B' hB' (by
        grind);
        exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.1, fun P hP => ⟨ this.choose_spec.2.2 P hP |>.1, this.choose_spec.2.2 P hP |>.2.1, eq_tsub_of_add_eq <| this.choose_spec.2.2 P hP |>.2.2 ⟩ ⟩;
      obtain ⟨P, hP⟩ : ∃ P ∈ parents, ∃ C, isCertificateFor state C B ∧ Reaches state P C := by
        rcases parents <;> aesop;
      obtain ⟨ C, hC₁, hC₂ ⟩ := hP.2;
      exact ⟨ C, hC₁, Reaches.step ( Reaches.refl _ ) ⟨ h_parents.2.2 P hP.1 |>.2.1, h_parents.2.2 P hP.1 |>.1, hB' ⟩ |> Reaches.trans <| hC₂ ⟩;
  exact h_ind ( B'.r - ( B.r + 2 ) ) ( Nat.zero_le _ ) B' h_in ( by rw [ add_tsub_cancel_of_le h_later ] )

/--
**Lemma 13 (paper Appendix D.3).**

> *In Mysticeti-Beluga, if an honest validator directly skips a
> round-`r` leader block `B_r^L`, then no honest validator commits
> `B_r^L`.*

Paper proof sketch: a direct skip occurs only if at least `2f + 1`
blocks in round `r + 1` do not reference `B_r^L`. But if `B_r^L`
is committed, then by the decision rule, at least `2f + 1` round
`r + 1` blocks reference it. The two `2f + 1`-quorums intersect in
at least one honest validator, who would have to equivocate —
contradiction.

In our Lean statement the "no commit" claim is reduced to
`view vid B.d ≠ Decision.ToCommit` for every honest `vid`, given
`directDecide system state B = Decision.ToSkip` and the protocol
fact that honest views agree with `directDecide` on this digest.
-/
theorem lemma13_no_commit
    (system : BlockSynchroniserSystem) {S} [SystemState S] (state : S)
    (view : ConsensusView)
    (B : Block) (h_direct_skip : directDecide system state B = Decision.ToSkip)
    (h_view_direct : ∀ vid, isHonestValidator system vid →
                       view vid B.d = directDecide system state B) :
    ∀ vid, isHonestValidator system vid →
      view vid B.d ≠ Decision.ToCommit := by
  -- By h_view_direct, every honest validator's view on B.d equals
  -- directDecide system state B = Decision.ToSkip (by h_direct_skip).
  -- Since Decision.ToSkip ≠ Decision.ToCommit, the conclusion follows.
  grind

/--
**Lemma 14 (paper Appendix D.3).**

> *In Mysticeti-Beluga, if an honest validator directly commits
> `B_r^L`, then no honest validator (directly or indirectly)
> decides to skip `B_r^L`.*

Paper proof sketch (two cases):
* *Direct skip.* A direct skip occurs only if at least `2f + 1`
  blocks in round `r + 1` do not reference `B_r^L`. But if `B_r^L`
  is committed, then by the decision rule, at least `2f + 1` round
  `r + 1` blocks reference it. The two `2f + 1`-quorums intersect
  in at least one honest validator, who would have to equivocate —
  contradiction.
* *Indirect skip.* An indirect skip occurs through a later leader
  `B_{r'}^L` with `r' > r + 2` whose causal history does not
  reference any certificate for `B_r^L`. But `B_r^L` is directly
  committed, so it has `2f + 1` certificates; by Lemma 12, every
  block in rounds `> r + 1` references one of them — contradiction.

In our Lean statement the "no skip" claim is reduced to
`view vid B.d ≠ Decision.ToSkip` for every honest `vid`, given
`directDecide system state B = Decision.ToCommit` and the protocol
fact that honest views agree with `directDecide` on this digest.
-/
theorem lemma14_no_skip
    (system : BlockSynchroniserSystem) {S} [SystemState S] (state : S)
    (view : ConsensusView)
    (B : Block) (h_direct_commit : directDecide system state B = Decision.ToCommit)
    (h_view_direct : ∀ vid, isHonestValidator system vid →
                       view vid B.d = directDecide system state B) :
    ∀ vid, isHonestValidator system vid →
      view vid B.d ≠ Decision.ToSkip := by
  -- By h_view_direct, every honest validator's view on B.d equals
  -- directDecide system state B = Decision.ToCommit (by h_direct_commit).
  -- Since Decision.ToCommit ≠ Decision.ToSkip, the conclusion follows.
  grind

/--
**Lemma 15 (paper Appendix D.3).**

> *In Mysticeti-Beluga, at most one leader block can be certified
> for any round `r`.*

This is a *specialization* of
[`Beluga.certified_unique`](../Beluga/Patterns.lean): restrict to
leader blocks (where `author = leaderOf system r`); uniqueness then
follows from the existing quorum-intersection chain.

Paper proof sketch:

> *Suppose two distinct leader blocks `B_{r,L_1}` and `B_{r,L_2}`
> both obtain `2f + 1` references from round `r + 1`. By quorum
> intersection, at least one honest validator must belong to both
> quorums, and thus would have referenced both blocks in round `r`.
> This contradicts the protocol rule that a validator references
> at most one block per proposer per round.*

The paper notes immediately after L15:

> **Corollary 1.** *No two honest validators commit distinct leader
> blocks in the same round.*

(Used in the base case of L16's backward induction below.)
-/
theorem lemma15_unique_cert
    (system : BlockSynchroniserSystem) {S} [SystemState S] (state : S)
    (h_no_eq : NoEquivocationInParents system state)
    (B₁ B₂ : Block)
    (h_lead₁ : isLeaderBlock system B₁) (h_lead₂ : isLeaderBlock system B₂)
    (h_same_round : B₁.r = B₂.r)
    (h_cert₁ : certified system state B₁) (h_cert₂ : certified system state B₂)
    -- Additional BFT hypotheses (passed through to `certified_unique`):
    (hN : system.n = 3 * system.f + 1)
    (h_B₁_in : B₁ ∈ SystemState.blocks state)
    (h_B₂_in : B₂ ∈ SystemState.blocks state)
    (h_authors_valid : ∀ B ∈ SystemState.blocks state,
      ∃ pair ∈ system.validators, pair.1 = B.author)
    (h_byz_bound : (system.validators.filter (fun p => p.2 = false)).length
      ≤ system.f) :
    B₁ = B₂ := by
  -- Specialization of Beluga.certified_unique: leader blocks share author by
  -- definition (both authored by leaderOf system B₁.r = leaderOf system B₂.r).
  have h_same_author : B₁.author = B₂.author := by
    unfold isLeaderBlock at h_lead₁ h_lead₂
    rw [h_lead₁, h_lead₂, h_same_round]
  exact certified_unique system state h_no_eq B₁ B₂ h_cert₁ h_cert₂ h_same_author h_same_round
    hN h_B₁_in h_B₂_in h_authors_valid h_byz_bound

/--
**Lemma 16 (paper Appendix D.3).**

> *In Mysticeti-Beluga, all honest validators decide a consistent
> status for each round leader block.*

Paper proof (verbatim):

> *Consider two honest validators `v_i` and `v_j`, and let `n` be
> the highest round in which `v_i` commits a leader block. We prove
> by backward induction that for every round `x ≤ n`, both
> validators assign the same status to `B_x^L`.*
>
> *Base case (`x = n`).* Validator `v_i` commits `B_n^L`. By Lemma
> 14, `v_j` cannot skip it and must also commit it. By Corollary 1
> (no two honest validators commit distinct leader blocks in the
> same round), both commit the same block.
>
> *Inductive step.* Assume the statement holds for all rounds in
> `(k, n]`. Consider round `k`. If either validator directly commits
> or directly skips `B_k^L`, the other must make the same decision
> by Lemma 13 and Lemma 14. Otherwise, both decisions are indirect
> and derived from a later committed leader. Let `k_i` and `k_j` be
> the rounds of the first such commits for `v_i` and `v_j`,
> respectively. By the induction hypothesis, `k_i = k_j`, and both
> validators commit the same leader block. Since indirect decisions
> depend only on the causal history of that block, both validators
> derive the same decision for `B_k^L`.

**Mechanization note.** Our `view.Consistent` only requires that
two non-`Undecided` honest views agree (the safety claim), not the
fuller "decide on the same set of leader blocks" claim used in the
paper's induction. The two are bridged by **decision completeness**
(see `h_decision_complete` on `theorem7_consensus_safety` below) —
a liveness consequence the paper invokes silently.

**Protocol-invariant hypothesis:**
- `h_view_traceback` — every non-`Undecided` honest view on a digest
  `d` traces back to a leader block `B` with `B.d = d` in the state
  whose `directDecide` is non-`Undecided`. This captures the protocol
  invariant that all consensus decisions originate from direct
  DAG-pattern observations on leader blocks.
-/
theorem lemma16_consistent_status
    (system : BlockSynchroniserSystem) {S} [SystemState S] (state : S)
    (view : ConsensusView)
    (h_view_direct : ∀ vid B, isHonestValidator system vid →
                       isLeaderBlock system B → B ∈ SystemState.blocks state →
                       directDecide system state B ≠ Decision.Undecided →
                       view vid B.d = directDecide system state B)
    -- Protocol invariant: every non-Undecided honest view on digest d
    -- traces back to a leader block B with B.d = d in the state whose
    -- directDecide is non-Undecided.
    (h_view_traceback : ∀ vid d, isHonestValidator system vid →
        view vid d ≠ Decision.Undecided →
        ∃ B, isLeaderBlock system B ∧ B ∈ SystemState.blocks state ∧
          directDecide system state B ≠ Decision.Undecided ∧ B.d = d) :
    view.Consistent system := by
  -- Unfold consistency: for any digest d and honest validators vid₁, vid₂,
  -- if both have non-Undecided views on d, they must agree.
  intro d vid₁ vid₂ h_honest₁ h_honest₂ h_ne₁ h_ne₂
  -- By h_view_traceback, vid₁'s non-Undecided view on d traces back to
  -- a leader block B_w with directDecide non-Undecided. By h_view_direct,
  -- both honest validators' views on B_w.d equal directDecide, hence agree.
  have h_exists_block : ∃ B, isLeaderBlock system B ∧
      B ∈ SystemState.blocks state ∧
      directDecide system state B ≠ Decision.Undecided ∧
      B.d = d := h_view_traceback vid₁ d h_honest₁ h_ne₁
  obtain ⟨B_w, h_leader, h_mem, h_dd, h_digest⟩ := h_exists_block
  have hv₁ := h_view_direct vid₁ B_w h_honest₁ h_leader h_mem h_dd
  have hv₂ := h_view_direct vid₂ B_w h_honest₂ h_leader h_mem h_dd
  rw [h_digest] at hv₁ hv₂
  rw [hv₁, hv₂]

/--
**Theorem 7 (paper Appendix D.3) — Consensus safety.**

> *In Mysticeti-Beluga, all honest validators order transactions
> consistently.*

Paper proof (verbatim):

> *By Lemma 16, all honest validators decide a consistent status for
> each round leader block, meaning that all honest validators
> decide identical to-commit leader blocks. According to the
> consensus logic employed by Mysticeti-Beluga, all honest
> validators will order to-commit leader blocks and their causal
> history block consistently. Therefore, for transactions included
> in the ordered blocks, all honest validators order them
> consistently.*

**Mechanization notes:**

- The paper's "decide identical leader blocks" overstates Lemma 16,
  which only gives *consistency* (no two honest validators decide
  non-`Undecided` differently) — not full *equality* of decided
  sets, which is a liveness property. We surface
  `h_decision_complete` as an explicit hypothesis to bridge the gap.

- "Transaction ordering respects view equality" is silently relied
  on. We surface this as `h_order_from_view`. For the `belugaTrace`
  instantiation a concrete realization is provided in
  `Beluga/Order.lean` (`belugaTransactionOrder` +
  `accepted_implies_in_belugaTransactionOrder`).

**Protocol-invariant hypothesis:**
- `h_decision_complete` — decision completeness: if one honest
  validator's view on a digest is `Undecided`, then all honest
  validators' views on that digest are `Undecided` (and vice versa).
  This is the liveness-derived property that honest validators
  eventually all decide the same way, upgrading `Consistent`
  (no conflicting non-`Undecided`) to full view equality.
-/
theorem theorem7_consensus_safety
    (system : BlockSynchroniserSystem) {S} [SystemState S] (_state : S)
    (view : ConsensusView) (order : TransactionOrder)
    (h_view_consistent : view.Consistent system)
    (h_order_from_view :
      -- transaction ordering is derived consistently from the consensus
      -- view: if two honest validators have the same view, their orders
      -- are consistent prefixes of each other.
      ∀ vid₁ vid₂, isHonestValidator system vid₁ →
                   isHonestValidator system vid₂ →
                   (∀ d, view vid₁ d = view vid₂ d) →
                   (order vid₁).isPrefixOf (order vid₂) ∨
                   (order vid₂).isPrefixOf (order vid₁))
    -- Protocol invariant (decision completeness): if one honest
    -- validator's view on digest d is Undecided, then so is every other
    -- honest validator's view (and vice versa). This upgrades
    -- ConsensusView.Consistent (no conflicting non-Undecided) to full
    -- view equality for honest validators.
    (h_decision_complete : ∀ vid₁ vid₂ d,
        isHonestValidator system vid₁ →
        isHonestValidator system vid₂ →
        (view vid₁ d = Decision.Undecided ↔ view vid₂ d = Decision.Undecided)) :
    order.Consistent system := by
  -- Paper argument: By Lemma 16, all honest validators assign identical
  -- decisions to each leader block. Combined with h_order_from_view
  -- (transaction ordering respects view equality), we obtain consistent
  -- transaction orders.
  intro vid₁ vid₂ h_honest₁ h_honest₂
  apply h_order_from_view vid₁ vid₂ h_honest₁ h_honest₂
  intro d
  -- From h_decision_complete + h_view_consistent: either both views are
  -- Undecided (and hence equal), or both are non-Undecided and equal
  -- (by consistency).
  have h_complete : view vid₁ d = Decision.Undecided ↔
      view vid₂ d = Decision.Undecided :=
    h_decision_complete vid₁ vid₂ d h_honest₁ h_honest₂
  by_cases h₁ : view vid₁ d = Decision.Undecided
  · rw [h₁, h_complete.mp h₁]
  · by_cases h₂ : view vid₂ d = Decision.Undecided
    · exact absurd (h_complete.mpr h₂) h₁
    · exact h_view_consistent d vid₁ vid₂ h_honest₁ h_honest₂ h₁ h₂

/-! ## belugaTrace-specialised wrappers

For the executable `belugaTrace` instantiation, the four
protocol-invariant hypotheses on L12 / L15
(`AdmissionWellFormed`, `NoEquivocationInParents`, the
honest-author uniqueness assumption, the authors-are-registered side
condition) are not assumptions: they are bundled in
`Mysticeti.MysticetiSafetyInv` and proved by
`belugaTrace_satisfies_mysticetiSafetyInv` (modulo the
`authorsValid` conjunct, queued for delegation).

These wrappers consume the bundle and re-state L12 / L15 against
`belugaTrace`, leaving only the genuine BFT side conditions (`hN`,
`h_byz_bound`, `hids`) — paper assumptions that cannot be derived
from the executable trace. -/

/-- **Lemma 12 (paper Appendix D.3) for the Beluga trace.**

belugaTrace specialisation of `lemma12_cert_persistence`. The four
protocol-invariant hypotheses (`h_no_eq`, `h_admission`,
`h_authors_valid`, `h_honest_unique`) are discharged from
[`belugaTrace_satisfies_mysticetiSafetyInv`](SafetyInvariant.lean). -/
theorem lemma12_cert_persistence_belugaTrace
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (hN : system.n = 3 * system.f + 1)
    (h_byz_bound : (system.validators.filter (fun p => p.2 = false)).length
      ≤ system.f)
    (k : Nat)
    (B : Block) (h_B : B ∈ (Beluga.belugaTrace system k).blocks)
    (h_cert : ∃ certs : List Block,
                certs.length ≥ 2 * system.f + 1 ∧
                certs.Nodup ∧
                (certs.map (·.author)).Nodup ∧
                ∀ C ∈ certs, isCertificateFor (Beluga.belugaTrace system k) C B)
    (B' : Block) (h_in : B' ∈ (Beluga.belugaTrace system k).blocks)
    (h_later : B'.r > B.r + 1) :
    ∃ C, isCertificateFor (Beluga.belugaTrace system k) C B ∧
         Reaches (Beluga.belugaTrace system k) B' C := by
  have h_inv := belugaTrace_satisfies_mysticetiSafetyInv system hids k
  exact lemma12_cert_persistence system (Beluga.belugaTrace system k)
    h_inv.noEquivocation h_inv.admission hN h_inv.authorsValid h_byz_bound
    (fun B₁ hB₁ B₂ hB₂ _ => h_inv.uniqueByAuthorRound B₁ hB₁ B₂ hB₂)
    B h_B h_cert B' h_in h_later

/-- **Lemma 15 (paper Appendix D.3) for the Beluga trace.**

belugaTrace specialisation of `lemma15_unique_cert`. The four
protocol-invariant hypotheses (`h_no_eq`, `h_authors_valid`,
`h_byz_bound` is kept since it is a system-wide BFT side condition)
are discharged from
[`belugaTrace_satisfies_mysticetiSafetyInv`](SafetyInvariant.lean). -/
theorem lemma15_unique_cert_belugaTrace
    (system : BlockSynchroniserSystem)
    (hids : ValidIds system)
    (hN : system.n = 3 * system.f + 1)
    (h_byz_bound : (system.validators.filter (fun p => p.2 = false)).length
      ≤ system.f)
    (k : Nat)
    (B₁ B₂ : Block)
    (h_lead₁ : isLeaderBlock system B₁) (h_lead₂ : isLeaderBlock system B₂)
    (h_same_round : B₁.r = B₂.r)
    (h_cert₁ : Beluga.certified system (Beluga.belugaTrace system k) B₁)
    (h_cert₂ : Beluga.certified system (Beluga.belugaTrace system k) B₂)
    (h_B₁_in : B₁ ∈ (Beluga.belugaTrace system k).blocks)
    (h_B₂_in : B₂ ∈ (Beluga.belugaTrace system k).blocks) :
    B₁ = B₂ := by
  have h_inv := belugaTrace_satisfies_mysticetiSafetyInv system hids k
  exact lemma15_unique_cert system (Beluga.belugaTrace system k)
    h_inv.noEquivocation B₁ B₂ h_lead₁ h_lead₂ h_same_round
    h_cert₁ h_cert₂ hN h_B₁_in h_B₂_in h_inv.authorsValid h_byz_bound

end Safety
end Mysticeti
end BlockSynchroniser
