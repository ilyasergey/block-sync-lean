/-
 Copyright Ilya Sergey

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

namespace BlockSynchroniser

-- Basic types
abbrev ValidatorId := Nat
abbrev Round := Nat
abbrev BlockDigest := Nat -- Block digest (could be a hash in practice)
abbrev Transaction := String -- Generic transaction type

-- Block structure
structure Block where
  r : Round -- the round where B is created
  author : ValidatorId -- the validator creating B, indexed by numbers
  d : BlockDigest -- the digest of B
  parents : List BlockDigest -- the connected parent blocks (in digests)
  payload : List Transaction -- a list of transactions
  deriving Repr, DecidableEq

-- Validator state (without ID and honesty - those are in the system)
structure Validator where
  acceptedBlocks : List BlockDigest -- accepted block digests
  storedBlocks : List BlockDigest -- stored block digests
  deriving Repr, DecidableEq

-- Operations that validators can perform
inductive ValidatorOperation where
  | block_propose (author : ValidatorId) (block : Block) (round : Round) : ValidatorOperation
  | block_accept (id : ValidatorId) (d : BlockDigest) : ValidatorOperation
  | block_store (id : ValidatorId) (block : Block) : ValidatorOperation
  deriving Repr

-- Block synchroniser system
structure BlockSynchroniserSystem where
  n : Nat -- total number of validators
  f : Nat -- maximum number of Byzantine validators
  k : Nat -- minimum number of parent blocks required
  validators : List (ValidatorId × Bool) -- mapping from ID to honesty status

  -- Properties of the system
  honestMajority: n ≥ 3 * f + 1
  -- All validators ids are unique
  validatorIdsUnique:
    let validatorIds := validators.map (fun (vid, _) => vid)
    validatorIds.eraseDups.length = validatorIds.length
  -- n is the number of validators
  validatorCountCorrect: n = validators.length
  deriving Repr

-- Properties and invariants
def isByzantineValidator (system : BlockSynchroniserSystem) (id : ValidatorId) : Bool :=
  match system.validators.find? (fun (vid, _) => vid = id) with
  | some (_, isHonest) => !isHonest
  | none => false

def isHonestValidator (system : BlockSynchroniserSystem) (id : ValidatorId) : Bool :=
  match system.validators.find? (fun (vid, _) => vid = id) with
  | some (_, isHonest) => isHonest
  | none => false

namespace SystemState

-- SystemState type class, allows for extensibility of the system state
class SystemState (S : Type) where
  validators : S → List (ValidatorId × Validator)
  blocks : S → List Block
  emittedOperations : S → List ValidatorOperation

-- Default SystemState implementation
structure DefaultSystemState where
  validators : List (ValidatorId × Validator) -- mapping from ID to validator state
  blocks : List Block -- all blocks seen in the system
  emittedOperations : List ValidatorOperation -- operations always remain available

instance : SystemState DefaultSystemState where
  validators s := s.validators
  blocks s := s.blocks
  emittedOperations s := s.emittedOperations


def getValidatorById {S} [SystemState S] (state : S) (id : ValidatorId) : Option Validator :=
  (SystemState.validators state).find? (fun (vid, _) => vid = id) |>.map (fun (_, validator) => validator)

def getBlockByDigest {S} [SystemState S] (state : S) (digest : BlockDigest) : Option Block :=
  (SystemState.blocks state).find? (fun b => b.d = digest)

-- Path definition: a path is a list of block digests representing a chain of parent relationships
def Path := List BlockDigest

-- Path validity: a path is valid if each consecutive pair represents a parent-child relationship
def isValidPath {S} [SystemState S] (state : S) (path : Path) : Bool :=
  match path with
  | [] | [_] => true
  | child :: parent :: rest =>
    match (SystemState.blocks state).find? (fun b => b.d = child) with
    | none => false
    | some childBlock => parent ∈ childBlock.parents && isValidPath state (parent :: rest)

-- Causal relation: holds if all blocks in the list are transitive ancestors of the given block
-- A block B' is a transitive ancestor of B if there exists a finite path from B to B' through parent relationships
def causal {S} [SystemState S] (state : S) (block : Block) (ancestors : List Block) : Prop :=
  ∀ ancestor, ancestor ∈ ancestors ->
    ancestor.d = block.d ∨
    ∃ path : Path,
      path.head? = some block.d ∧
      path.getLast? = some ancestor.d ∧
      isValidPath state path

-- Block validity conditions
def hasValidParents {S} [SystemState S] (system : BlockSynchroniserSystem) (block : Block) (state : S) : Bool :=
  block.parents.length >= system.k &&
  block.parents.all (fun parentDigest =>
    match getBlockByDigest state parentDigest with
    | some parent => parent.r = block.r - 1
    | none => false)

-- Block validity conditions: non-empty, has valid parents
def isBlockValid {S} [SystemState S] (system : BlockSynchroniserSystem) (block : Block) (state : S) : Bool :=
  block.r > 0 && -- non-empty, ever-growing
  hasValidParents system block state

-- This invariant ensures that the number of Byzantine validators is at most f.
def atMostFByzantine {S} [SystemState S] (system : BlockSynchroniserSystem) (_state : S) : Bool :=
  let byzantineCount := system.validators.filter (fun (_, isHonest) => !isHonest) |>.length
  byzantineCount ≤ system.f

-- This invariant ensures that the number of Byzantine validators is at most f.
-- This is a necessary condition for the system to be able to tolerate f
-- Byzantine validators.
def allValidatorsPresent {S} [SystemState S] (system : BlockSynchroniserSystem) (state : S) : Bool :=
  (SystemState.validators state).length = system.n &&
  (SystemState.validators state).all (fun (vid, _) => system.validators.any (fun (sid, _) => sid = vid))

-- Main system invariant: at most f Byzantine validators, all validators
-- present, and all blocks valid.
def systemInvariant {S} [SystemState S] (system : BlockSynchroniserSystem) (state : S) : Bool :=
  atMostFByzantine system state &&
  allValidatorsPresent system state &&
  -- all blocks are valid
  (SystemState.blocks state).all (fun b => isBlockValid system b state) &&
  -- all digests are unique
  (SystemState.blocks state).all (fun b => (SystemState.blocks state).all (fun b' => b.d = b'.d -> b = b'))

-- A trace is defined as a function from ℕ to system states
def Trace (S : Type) [SystemState S] := Nat → S

-- A trace is valid if it satisfies the system invariant
def isValidTrace {S} [SystemState S] system (trace : Trace S) :=
  forall i, systemInvariant system (trace i)

-- Trace induction principle
theorem traceInduction {S} [SystemState S]
  (P : BlockSynchroniserSystem → S → Prop)
  system (trace : Trace S)
  (round : P system (trace 0))
  (step : forall i, P system (trace i) → P system (trace (i + 1))) :
  forall i, P system (trace i) :=
  fun i => Nat.rec round (fun i ih => step i ih) i

end SystemState

---------------------------------------------------------------------
-- Auxiliary definitions
---------------------------------------------------------------------

-- Helper function to extract author from a block_accept operation in a given
-- round
def getAuthorFromAccept (operations : List ValidatorOperation) (round : Round) (op : ValidatorOperation) : Option ValidatorId :=
  match op with
  | .block_accept _ blockDigest =>
    -- Find the block_propose operation that created this block digest in round r
    operations.find? (fun op' =>
      match op' with | .block_propose _author block _ => block.d = blockDigest && block.r = round
                     | _ => false)
    -- Extract the author ID from the found block_propose operation
    |>.bind (fun op' => match op' with | .block_propose author _ _ => some author | _ => none)
  | _ => none


---------------------------------------------------------------------
-- Properties of block synchroniser system
---------------------------------------------------------------------

namespace Properties

open SystemState

-- Property 1: Validity: If an honest validator V_i invokes
-- block_propose_i(B,r), then every honest validator eventually outputs
-- block_accept(B.d)
def blockSynchroniserValidity {S} [SystemState S] (system : BlockSynchroniserSystem) (trace: Trace S) : Prop :=
  ∀ round k (o : Nat) vid block,
    -- take a snapshot and emitted operations at the moment k
    let state_k := trace k
    let operations := SystemState.emittedOperations state_k
    -- some operation o is the propose operation from validator i
    operations[o]? = some (.block_propose vid block round) ->
    -- i is an honest validator
    isHonestValidator system vid ->
    -- for any honest validator vid'
      ∀ vid', isHonestValidator system vid' ->
        -- there exists a moment k' and an operation o'
        ∃ k' ≥ k, ∃ o' : Nat,
        -- such that the operation o' is the accept operation from validator vid' in the same round
        let state_k' := trace k'
        let operations' := SystemState.emittedOperations state_k'
        operations'[o']? = some (.block_accept vid' block.d)

-- Property 2a: Progress I: In each round, at least 2f + 1 validators (not
-- necessarily honest ones) invoke block_propose to disseminate some blocks.
def blockSynchroniserProgressI {S} [SystemState S] (system : BlockSynchroniserSystem) (trace: Trace S) : Prop :=
  ∀ round, -- for any round
    ∃ k, -- there exists a moment k such that
      let state_k := trace k
      let operations := SystemState.emittedOperations state_k
      -- at least 2f+1 unique validators invoke block_propose in round
      let uniqueProposers := operations.filter (fun op =>
        match op with | .block_propose _ _ r => r = round | _ => false)
        |>.map (fun op =>
        match op with | .block_propose vid _ _ => vid | _ => 0)
        |>.eraseDups.length
      uniqueProposers ≥ 2 * system.f + 1

-- Property 2b: Progress II: In each round, each honest validator outputs
-- block_accept for accepting at least 2f + 1 disseminated blocks.
def blockSynchroniserProgressII {S} [SystemState S] (system : BlockSynchroniserSystem) (trace: Trace S) : Prop :=
  ∀ round, -- for any round
    ∃ k, -- there exists a moment k such that
      let state_k := trace k
      let operations := SystemState.emittedOperations state_k
      -- each honest validator accepts at least 2f+1 disseminated blocks
      ∀ vid, isHonestValidator system vid ->
        let acceptOperationsByVid := operations.filter (fun op =>
          match op with | .block_accept vid' _ => vid' = vid | _ => false)
        let authorsOfAcceptedBlocks := acceptOperationsByVid.map (getAuthorFromAccept operations round)
                         |>.filterMap id |>.eraseDups
        authorsOfAcceptedBlocks.length ≥ 2 * system.f + 1

-- Property 3: Block availability: If an honest validator V_i outputs
-- block_accept_i(B.d) then V_i eventually outputs block_store_i(B) .
def blockSynchroniserAvailability {S} [SystemState S] (system : BlockSynchroniserSystem) (trace: Trace S) : Prop :=
  ∀ k (o : Nat) vid blockDigest,
    -- take a snapshot and emitted operations at the moment k
    let state_k := trace k
    let operations := SystemState.emittedOperations state_k
    -- some operation o is the accept operation from validator i
    operations[o]? = some (.block_accept vid blockDigest) ->
    -- i is an honest validator
    isHonestValidator system vid ->
    -- there exists a moment k' and an operation o'
    ∃ k' ≥ k, ∃ o' : Nat, ∃ block : Block,
    -- such that the operation o' is the store operation from validator vid
    let state_k' := trace k'
    let operations' := SystemState.emittedOperations state_k'
    operations'[o']? = some (.block_store vid block) ∧
    -- where block has the same digest as the accepted one
    block.d = blockDigest

-- Property 4: Casual availability: If an honest validator V_i outputs
-- block_accept_i (B.d), then for every block B' ∈ causal(B), V_i eventually
-- outputs block_accept_i (B'.d). Here, causal (B) represents B's causal history
-- (i.e., all blocks for which there is a connection or path from B to them).
def blockSynchroniserCausalAvailability {S} [SystemState S] (system : BlockSynchroniserSystem) (trace: Trace S) : Prop :=
  ∀ k (o : Nat) vid blockDigest,
    -- take a snapshot and emitted operations at the moment k
    let state_k := trace k
    let operations := SystemState.emittedOperations state_k
    -- some operation o is the accept operation from validator i
    operations[o]? = some (.block_accept vid blockDigest) ->
    -- i is an honest validator
    isHonestValidator system vid ->
    -- get the block that was accepted and for every block B' in its causal history
    ∀ block : Block, getBlockByDigest state_k blockDigest = some block ->
      ∀ block' : Block, causal state_k block [block'] ->
        -- there exists a moment k' and an operation o'
        ∃ k' ≥ k, ∃ o' : Nat,
        -- such that the operation o' is the accept operation from validator vid in the same round
        let state_k' := trace k'
        let operations' := SystemState.emittedOperations state_k'
        operations'[o']? = some (.block_accept vid block'.d)

-- Helper: all honest validators eventually store all blocks in the given set
-- at some point of time after k
def allHonestValidatorsEventuallyStore {S} [SystemState S] (system : BlockSynchroniserSystem)
    (trace: Trace S) (commonSet : List Block) (k : Nat) : Prop :=
  ∀ vid, isHonestValidator system vid -> -- any honest validator
    ∀ block, block ∈ commonSet -> -- for any block in the commonSet
      ∃ k' ≥ k, ∃ o' : Nat,
        let state_k' := trace k'
        let operations' := SystemState.emittedOperations state_k'
        operations'[o']? = some (.block_store vid block)

-- Helper: compute unique authors of blocks in the common set
def authorsInCommonSet (commonSet : List Block) : List ValidatorId :=
  commonSet.map (fun block => block.author) |>.eraseDups

-- Property 5: 2/3-Available common set: For each round r, all honest validators
-- eventually store (via block_store) a common subset containing blocks from at
-- least 2f + 1 validators.
def blockSynchroniserCommonSet {S} [SystemState S] (system : BlockSynchroniserSystem) (trace: Trace S) : Prop :=
  ∀ round, -- for any round
    ∃ commonSet, -- there exists a common set of blocks
      -- All blocks in commonSet have the same round
      commonSet.all (fun block => block.r = round) ∧
      -- the common subset contains blocks from at least 2f + 1 validators in round r
      (authorsInCommonSet commonSet).length ≥ 2 * system.f + 1
      ∧
      -- All validators eventually store it at the same round
      ∃ k, allHonestValidatorsEventuallyStore system trace commonSet k

end Properties
end BlockSynchroniser
