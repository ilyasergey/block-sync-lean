/-
Copyright Ilya Sergey

Licensed under the Apache License, Version 2.0.

The four properties of Definition 1 (paper §2.1). Wording in each docstring is
the verbatim paper text, used as a calibration check during review.
-/
import BlockSynchroniser.System
import BlockSynchroniser.State
import BlockSynchroniser.Causal
import BlockSynchroniser.Trace

namespace BlockSynchroniser
namespace Properties

variable {S : Type} [SystemState S]

/--
**Definition 1.1 — Round-Progression.**

In each global round `r` of the system, at least `2f + 1` validators (not
necessarily honest ones) invoke `block_propose` to create and disseminate
their blocks. In other words, for each given `r ≥ 0`, at least `2f + 1`
produce blocks that have `r` as their round.
-/
def RoundProgression (system : BlockSynchroniserSystem) (trace : Trace S) : Prop :=
  ∀ round, ∃ k,
    let proposers : List ValidatorId :=
      (opsAt trace k).filterMap (fun op =>
        match op with
        | .block_propose vid _ r => if r = round then some vid else none
        | _ => none)
      |>.eraseDups
    proposers.length ≥ 2 * system.f + 1

/--
**Definition 1.2 — Round-Termination.**

For each global round `r` of the system, every honest validator eventually
outputs `block_accept` for the blocks produced in this round by at least
`2f+1` validators. That is, for each `r ≥ 0`, each honest validator can
accept block proposals, whose assigned round is `r`, from at least `2f+1`
different validators.
-/
def RoundTermination (system : BlockSynchroniserSystem) (trace : Trace S) : Prop :=
  ∀ round vid, isHonestValidator system vid →
    ∃ k,
      let ops := opsAt trace k
      let acceptedAuthors : List ValidatorId :=
        ops.filterMap (fun op =>
          match op with
          | .block_accept vid' d =>
            if vid' = vid then authorOfDigest ops round d else none
          | _ => none)
        |>.eraseDups
      acceptedAuthors.length ≥ 2 * system.f + 1

/--
**Definition 1.3 — Block availability.**

For some block `B` produced in round `r`, if an honest validator `v_i` outputs
`block_accept_i(B.d)`, then `v_i` eventually outputs `block_store_i(B)`.
-/
def BlockAvailability (system : BlockSynchroniserSystem) (trace : Trace S) : Prop :=
  ∀ k vid d, isHonestValidator system vid →
    HasAccepted (trace k) vid d →
    Eventually trace k (fun _ state => ∃ B : Block, HasStored state vid B ∧ B.d = d)

/--
**Definition 1.4 — Causal availability.**

For some block `B` produced in round `r`, if an honest validator `v_i` outputs
`block_accept_i(B.d)`, then for every block `B' ∈ causal(B)`, `v_i` eventually
outputs `block_accept_i(B'.d)`. Here, `causal(B)` represents `B`'s causal
history (i.e., all blocks for which there is a connection or path from `B` to
them).
-/
def CausalAvailability (system : BlockSynchroniserSystem) (trace : Trace S) : Prop :=
  ∀ k vid d B, isHonestValidator system vid →
    HasAccepted (trace k) vid d →
    getBlockByDigest (trace k) d = some B →
    ∀ B', Reaches (trace k) B B' →
      Eventually trace k (fun _ state => HasAccepted state vid B'.d)

/--
**Definition 1 — Block synchronizer (paper §2.1, conjunction of 1.1–1.4).**

A trace is a *block synchronizer* iff it satisfies all four properties.
This is the abstract specification; paper Theorems 1–4 (§5) prove that the
Beluga protocol's induced trace is a `BlockSynchronizer`.
-/
def BlockSynchronizer (system : BlockSynchroniserSystem) (trace : Trace S) : Prop :=
  RoundProgression   system trace ∧
  RoundTermination   system trace ∧
  BlockAvailability  system trace ∧
  CausalAvailability system trace

end Properties
end BlockSynchroniser
