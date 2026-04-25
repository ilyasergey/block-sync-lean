/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

Beluga's main theorems (paper §5).

Status: theorem *statements* against `belugaTrace`. Proofs are `sorry` with
`PROVIDED SOLUTION` sketches drawn directly from the paper's prose. They
will be filled by hand or via Aristotle in subsequent rounds.

Theorems 3 and 4 (Round-Progression, Round-Termination) are stated purely
in terms of the abstract Definition-1 properties from `Properties.lean`.
Theorems 1 and 2 (Block availability, Causal availability) likewise.

Lemmas 1 and 2 are timing claims (`3Δ`-bounded round-entry and round
latency after GST). The current `Trace` doesn't expose wall-clock time;
those statements are placeholders pending the timing model from
`docs/formalization-plan.md` (see "step-to-time map" notes).
-/
import BlockSynchroniser.System
import BlockSynchroniser.Properties
import BlockSynchroniser.Beluga.Protocol

namespace BlockSynchroniser
namespace Beluga
namespace Theorems

open Properties

/-! ## Section 5 — Main theorems

Each theorem says "the trace induced by Beluga's executable protocol
satisfies Definition 1.X". The statements are stated against the
*relational* `HonestStep` semantics — `belugaTrace` (the executable
schedule) is one specific witness, but the theorems generalize to any
trace whose every step satisfies `HonestStep`. -/

/--
**Lemma 1 (paper §5).**
*After GST, all honest validators will enter the same round within 3Δ.*

Stated abstractly here: there exists a step `k` after which every honest
validator's local `currentRound` agrees with every other honest
validator's. The wall-clock `3Δ` bound is a placeholder; once a
step-to-time map lands, replace `∃ k` with `∀ t ≥ system.GST + 3*system.Δ`.

PROVIDED SOLUTION (paper §5)
W.l.o.g., assume round `r` is the last round entered by honest validators
before GST. After GST, the message delay between honest validators is
bounded by Δ. Thus, all honest validators must receive at least one
round-`r` block from honest validator `v_i` by time `GST + Δ`. Every
honest validator can synchronize all `B_i^r`'s parent blocks and missing
ancestors via the pull protocol within `2Δ`. Consequently, all honest
validator can accept at least `2f+1` round-`r-1` blocks and enter round
`r` by time `GST + 3Δ`.
-/
theorem lemma1_honest_round_entry
    (system : BlockSynchroniserSystem) :
    ∀ vid₁ vid₂,
      isHonestValidator system vid₁ = true →
      isHonestValidator system vid₂ = true →
      ∃ k,
        match (belugaTrace system k).getValidator vid₁,
              (belugaTrace system k).getValidator vid₂ with
        | some bv₁, some bv₂ => bv₁.currentRound = bv₂.currentRound
        | _, _ => False := by
  sorry

/--
**Lemma 2 (paper §5).**
*After GST, if an honest validator `v_i` enters round `r` at time `t_r`,
and all honest validators have created and disseminated their round `r`
blocks by time `t_r`, then all honest validators will be able to enter
round `r+1` by time `t_r + 3Δ`.*

Stated abstractly here as a "next round eventually entered" property
without a tight bound. Tightening to `t_r + 3Δ` requires the timing
model.

PROVIDED SOLUTION (paper §5)
By the lemma's hypothesis, `t_r` is the time when the slowest honest
validator creates and disseminates its round `r` block. By time
`t_r + Δ`, all honest validators receive the round `r` blocks from all
honest validators. Even though some honest validators may need to
synchronize missing ancestors to accept round `r` blocks, they can
accept these blocks via the pull protocol within `2Δ`. As a result,
all honest validators can accept at least `2f+1` round `r` blocks by
time `t_r + 3Δ`, and enter their round `r+1` block by time `t_r + 3Δ`.
-/
theorem lemma2_round_latency
    (system : BlockSynchroniserSystem) :
    ∀ vid r k,
      isHonestValidator system vid = true →
      (∃ bv, (belugaTrace system k).getValidator vid = some bv ∧ bv.currentRound = r) →
      ∃ k' ≥ k,
        ∃ bv, (belugaTrace system k').getValidator vid = some bv ∧
              bv.currentRound = r + 1 := by
  sorry

/--
**Theorem 1 (paper §5) — Beluga satisfies Block availability.**

*If an honest validator `v_i` outputs `block_accept_i(B.d)` for some block
`B` produced in round `r`, then `v_i` eventually outputs
`block_store_i(B)`.*

PROVIDED SOLUTION (paper §5)
In Beluga, an honest validator outputs `block_accept_i(B.d)` for some
block `B` in round `r` when `v_i` received `B`. As a result, `v_i` must
have stored `B`.
-/
theorem theorem1_block_availability
    (system : BlockSynchroniserSystem) :
    BlockAvailability system (belugaTrace system) := by
  sorry

/--
**Theorem 2 (paper §5) — Beluga satisfies Causal availability.**

*If an honest validator `v_i` outputs `block_accept_i(B.d)` for some block
`B`, then for every block `B' ∈ causal(B)`, `v_i` eventually outputs
`block_accept_i(B'.d)`.*

PROVIDED SOLUTION (paper §5)
In Beluga, an honest validator `v_i` outputs `block_accept_i(B.d)` for
some block `B` in round `r` when `v_i` received `B` and ensures all its
parents in round `r-1` are available — that is, `v_i` has either output
`block_accept_i` for the parent blocks or observed they are referenced
by at least `f+1` subsequent blocks (§4.3). In the latter case, the
parent blocks (denoted by a set `B^(r-1)`) are referenced by at least
`f+1` subsequent blocks, so by Beluga's push protocol, the creators of
these `f+1` subsequent blocks must have output `block_accept` for
`B^(r-1)`. By induction on causal depth, `v_i` can eventually receive
every `B' ∈ causal(B)` from some honest validator and output
`block_accept_i(B'.d)`.
-/
theorem theorem2_causal_availability
    (system : BlockSynchroniserSystem) :
    CausalAvailability system (belugaTrace system) := by
  sorry

/--
**Theorem 3 (paper §5) — Beluga satisfies Round-Progression.**

*For each round `r ≥ 0`, at least `2f+1` validators will create and
disseminate their round `r` blocks.*

PROVIDED SOLUTION (paper §5)
For the genesis round `0`, all validators will create and disseminate
their round `0` blocks. Thus, the lemma holds for round `0`. By
induction on `r`, at least `2f+1` validators will create and
disseminate their round `r` blocks. Moreover, for any previous round
`1 ≤ r'' ≤ r`, since Beluga's push protocol requires validators to
reference at least `2f+1` parent blocks from the previous round when
creating their round `r''` blocks, at least `2f+1` validators must have
created and disseminated their round `r''-1` blocks. By induction, at
least `2f+1` validators have created and disseminated their round `r''`
blocks for every `0 ≤ r'' ≤ r`.
-/
theorem theorem3_round_progression
    (system : BlockSynchroniserSystem) :
    RoundProgression system (belugaTrace system) := by
  sorry

/--
**Theorem 4 (paper §5) — Beluga satisfies Round-Termination.**

*For each round `r ≥ 0`, each honest validator accepts block proposals,
whose assigned round is `r`, from at least `2f+1` different validators.*

PROVIDED SOLUTION (paper §5)
For the genesis round `0`, since all honest validators create their
round `0` blocks, and round `0` blocks do not reference any blocks,
each honest validator can accept at least `2f+1` round `0` blocks.
The lemma holds for round `0`. In addition, by Theorem 3, for each
round `r ≥ 1`, at least `2f+1` validators will create and disseminate
their round `r` blocks. Each round `r` block consists of at least `f+1`
blocks created by honest validators. For these `f+1` honest validators,
according to Beluga's push protocol, they must output `block_accept` to
accept at least `2f+1` round `r-1` blocks. According to Theorem 1 and
Theorem 2, these round `r-1` blocks and their causal histories are
available to all honest validators. As a result, each honest validator
can accept at least `2f+1` round `r-1` blocks. By induction, each
honest validator can accept at least `2f+1` round `r` blocks for any
round `r ≥ 1`.
-/
theorem theorem4_round_termination
    (system : BlockSynchroniserSystem) :
    RoundTermination system (belugaTrace system) := by
  sorry

/--
**Beluga is a block synchronizer (corollary of Theorems 1–4).**

The headline statement of paper §5: Beluga's induced trace satisfies
all four properties of Definition 1.
-/
theorem belugaTrace_isBlockSynchronizer
    (system : BlockSynchroniserSystem) :
    BlockSynchronizer system (belugaTrace system) :=
  ⟨theorem3_round_progression system,
   theorem4_round_termination system,
   theorem1_block_availability system,
   theorem2_causal_availability system⟩

end Theorems
end Beluga
end BlockSynchroniser
