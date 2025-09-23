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

import Batteries.Data.HashMap
import Ssreflect.Lang
import Aesop

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

-- System state
structure SystemState where
  validators : List (ValidatorId × Validator) -- mapping from ID to validator state
  blocks : List Block -- all blocks seen in the system
  currentRound : Round
  deriving Repr

-- Block synchroniser system
structure BlockSynchroniserSystem where
  n : Nat -- total number of validators
  f : Nat -- maximum number of Byzantine validators
  k : Nat -- minimum number of parent blocks required
  validators : List (ValidatorId × Bool) -- mapping from ID to honesty status
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

def getValidatorById (state : SystemState) (id : ValidatorId) : Option Validator :=
  state.validators.find? (fun (vid, _) => vid = id) |>.map (fun (_, validator) => validator)

def getBlockByDigest (state : SystemState) (digest : BlockDigest) : Option Block :=
  state.blocks.find? (fun b => b.d = digest)

-- Path definition: a path is a list of block digests representing a chain of parent relationships
def Path := List BlockDigest

-- Path validity: a path is valid if each consecutive pair represents a parent-child relationship
def isValidPath (state : SystemState) (path : Path) : Bool :=
  match path with
  | [] | [_] => true
  | child :: parent :: rest =>
    match state.blocks.find? (fun b => b.d = child) with
    | none => false
    | some childBlock => parent ∈ childBlock.parents && isValidPath state (parent :: rest)

-- Causal relation: holds if all blocks in the list are transitive ancestors of the given block
-- A block B' is a transitive ancestor of B if there exists a finite path from B to B' through parent relationships
def causal (state : SystemState) (block : Block) (ancestors : List Block) : Prop :=
  ∀ ancestor, ancestor ∈ ancestors ->
    ancestor.d = block.d ∨
    ∃ path : Path,
      path.head? = some block.d ∧
      path.getLast? = some ancestor.d ∧
      isValidPath state path

-- Block validity conditions
def hasValidParents (system : BlockSynchroniserSystem) (block : Block) (state : SystemState) : Bool :=
  block.parents.length >= system.k &&
  block.parents.all (fun parentDigest =>
    match getBlockByDigest state parentDigest with
    | some parent => parent.r = block.r - 1
    | none => false)

-- Block validity conditions: non-empty, has valid parents
def isBlockValid (system : BlockSynchroniserSystem) (block : Block) (state : SystemState) : Bool :=
  block.r > 0 && -- non-empty, ever-growing
  hasValidParents system block state

-- This invariant ensures that the number of Byzantine validators is at most f.
def atMostFByzantine (system : BlockSynchroniserSystem) (_state : SystemState) : Bool :=
  let byzantineCount := system.validators.filter (fun (_, isHonest) => !isHonest) |>.length
  byzantineCount ≤ system.f

-- This invariant ensures that the number of Byzantine validators is at most f.
-- This is a necessary condition for the system to be able to tolerate f
-- Byzantine validators.
def allValidatorsPresent (system : BlockSynchroniserSystem) (state : SystemState) : Bool :=
  state.validators.length = system.n &&
  state.validators.all (fun (vid, _) => system.validators.any (fun (sid, _) => sid = vid))

-- Main system invariant: at most f Byzantine validators, all validators
-- present, and all blocks valid.
def systemInvariant (system : BlockSynchroniserSystem) (state : SystemState) : Bool :=
  atMostFByzantine system state &&
  allValidatorsPresent system state &&
  -- all blocks are valid
  state.blocks.all (fun b => isBlockValid system b state) &&
  -- all digests are unique
  state.blocks.all (fun b => state.blocks.all (fun b' => b.d = b'.d -> b = b'))

end BlockSynchroniser

---------------------------------------------------------------------
-- This namespace defines valid executions of the system.
---------------------------------------------------------------------
namespace BlockSynchroniser.Executions

-- Operations that validators can perform
inductive ValidatorOperation where
  | block_propose (id : ValidatorId) (block : Block) (round : Round) : ValidatorOperation
  | block_accept (id : ValidatorId) (d : BlockDigest) : ValidatorOperation
  | block_store (id : ValidatorId) (block : Block) : ValidatorOperation
  deriving Repr


-- System state with pending operations
structure SystemSnapshot where
  state : SystemState
  -- Operations always remain available
  pendingOperations : List ValidatorOperation
  deriving Repr

-- A trace is defined as a function from ℕ to system snapshots
def Trace := Nat → SystemSnapshot

-- A trace is valid if it satisfies the system invariant and currentRound does not decrease
def isValidTrace system (trace : Trace) :=
  forall i, systemInvariant system (trace i).state ∧
  (i > 0 → (trace i).state.currentRound ≥ (trace (i - 1)).state.currentRound)

-- Trace induction principle
theorem traceInduction
  (P : BlockSynchroniserSystem → SystemSnapshot → Prop)
  system (trace : Trace)
  (round : P system (trace 0))
  (step : forall i, P system (trace i) → P system (trace (i + 1))) :
  forall i, P system (trace i) :=
  fun i => Nat.rec round (fun i ih => step i ih) i

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

-- Property 1: Validity: If an honest validator V_i invokes
-- block_propose_i(B,r), then every honest validator eventually outputs
-- block_accept(B.d)
def blockSynchroniserValidity (system : BlockSynchroniserSystem) (trace: Trace) : Prop :=
  ∀ k (o : Nat) vid block round,
    -- take a snapshot and emitted operations at the moment k
    let ⟨_, operations⟩ := trace k
    -- some operation o is the propose operation from validator i
    operations[o]? = some (.block_propose vid block round) ->
    -- i is an honest validator
    isHonestValidator system vid ->
    -- for any honest validator vid'
      ∀ vid', isHonestValidator system vid' ->
        -- there exists a moment k' and an operation o'
        ∃ k', ∃ o' : Nat,
        -- such that the operation o' is the accept operation from validator vid'
        let ⟨_, operations'⟩ := trace k'
        k ≤ k' ∧ -- not sure if this is required
        operations'[o']? = some (.block_accept vid' block.d)


-- Property 2a: Progress A: In each round r, every honest validator eventually
-- outputs block_accept for blocks from at least 2f+1 validators.
/-
Notes: this property assumes that any snapshot has operations for rounds that do
not exceed the current round number.
 -/
def blockSynchroniserProgress (system : BlockSynchroniserSystem) (trace: Trace) : Prop :=
  ∀ r vid,
    -- for any round r and any honest validator vid
    isHonestValidator system vid ->
    -- there exists a moment k such that
    ∃ k,
      let ⟨ ⟨_, _, currentRound⟩ , operations⟩ := trace k
      currentRound = r -> -- the current round is r

      -- the validator vid has accepted blocks from at least 2f+1 validators in round r
      let blocksAcceptedByVid := operations.filter (fun op =>
          match op with | .block_accept vid' _ => vid' = vid | _ => false)

      -- For each accepted block, find the author by looking up the
      -- corresponding block_propose operation
      let authors := blocksAcceptedByVid.map (getAuthorFromAccept operations currentRound)
                     |>.filterMap id

      -- Filter out None values and extract the Some values
      let uniqueAuthors := authors.foldl (fun acc author =>
        if authors.any (fun a => a = author) then acc else acc + 1) 0

      uniqueAuthors ≥ 2 * system.f + 1

-- Property 2b: Progress B: For each round r, at least 2f+1 validators invoke
-- block_propose to disseminate their blocks.
def blockSynchroniserProgressB (system : BlockSynchroniserSystem) (trace: Trace) : Prop :=
  ∀ r, -- for any round r, there exists a moment k such that
    ∃ k,
      let ⟨ ⟨_, _, currentRound⟩ , operations⟩ := trace k
      -- the current round is r
      currentRound = r ->
      -- at least 2f+1 validators invoke block_propose in round r
      let proposeOperations := operations.filter (fun op =>
        match op with | .block_propose _ _ round => round = r | _ => false)
      let uniqueProposers := proposeOperations.map (fun op =>
        match op with | .block_propose vid _ _ => vid | _ => 0)
                    |>.eraseDups.length
      uniqueProposers ≥ 2 * system.f + 1

-- Property 3: Block availability: If an honest validator 𝑉_i outputs
-- block_accept_i(B.d), then 𝑉_i eventually outputs block_store_i(B).
def blockSynchroniserAvailability (system : BlockSynchroniserSystem) (trace: Trace) : Prop :=
  ∀ k (o : Nat) vid blockDigest,
    -- take a snapshot and emitted operations at the moment k
    let ⟨_, operations⟩ := trace k
    -- some operation o is the accept operation from validator i
    operations[o]? = some (.block_accept vid blockDigest) ->
    -- i is an honest validator
    isHonestValidator system vid ->
    -- there exists a moment k' and an operation o'
    ∃ k', ∃ o' : Nat, ∃ block : Block,
    -- such that the operation o' is the store operation from validator vid
    let ⟨_, operations'⟩ := trace k'
    k ≤ k' ∧
    operations'[o']? = some (.block_store vid block) ∧
    -- where block has the same digest as the accepted one
    block.d = blockDigest

-- Property 4: Casual availability: If an honest validator V_i outputs
-- block_accept_i (B.d), then for every block B' ∈ causal(𝐵), 𝑉_𝑖 eventually
-- outputs block_accept_i (B'.d), where causal (B) represents B's causal history
-- (i.e., all blocks for which there is a connection or path from B to them).
def blockSynchroniserCausalAvailability (system : BlockSynchroniserSystem) (trace: Trace) : Prop :=
  ∀ k (o : Nat) vid blockDigest,
    -- take a snapshot and emitted operations at the moment k
    let ⟨state, operations⟩ := trace k
    -- some operation o is the accept operation from validator i
    operations[o]? = some (.block_accept vid blockDigest) ->
    -- i is an honest validator
    isHonestValidator system vid ->
    -- get the block that was accepted and for every block B' in its causal history
    ∀ block : Block, getBlockByDigest state blockDigest = some block ->
      ∀ block' : Block, BlockSynchroniser.causal state block [block'] ->
        -- there exists a moment k' and an operation o'
        ∃ k', ∃ o' : Nat,
        -- such that the operation o' is the accept operation from validator vid
        let ⟨_, operations'⟩ := trace k'
        k ≤ k' ∧
        operations'[o']? = some (.block_accept vid block'.d)

-- Helper: all honest validators eventually store all blocks in the given set
def allHonestValidatorsEventuallyStore (system : BlockSynchroniserSystem) (trace: Trace) (commonSet : List Block) (k : Nat) : Prop :=
  ∀ vid, isHonestValidator system vid ->
    ∀ block, block ∈ commonSet ->
      ∃ k', ∃ o' : Nat,
        let ⟨_, operations'⟩ := trace k'
        k ≤ k' ∧
        operations'[o']? = some (.block_store vid block)

-- Helper: compute unique authors of blocks in the common set for a given round
def authorsInCommonSet (operations : List ValidatorOperation) (commonSet : List Block) (r : Round) : List ValidatorId :=
  -- for each block in the common set
  commonSet.map (fun block =>
    -- find the block_propose operation that created this block in round r
    operations.find? (fun op =>
      match op with | .block_propose _ block' _ => block'.d = block.d ∧ block'.r = r | _ => false)
    -- extract the author ID from the found block_propose operation
    |>.bind (fun op => match op with | .block_propose author _ _ => some author | _ => none))
  |>.filterMap id  -- filter out None values to get only valid author IDs
  |>.eraseDups -- remove duplicate authors to get unique validators

-- Property 5: 2/3-Available common set: For each round r, all honest validators
-- eventually store (via block_store) a common subset containing blocks from at
-- least 2f + 1 validators.
def blockSynchroniserCommonSet (system : BlockSynchroniserSystem) (trace: Trace) : Prop :=
  ∀ r, -- for any round r
    -- there exists a common set of blocks and a moment k
    ∃ commonSet k,
      allHonestValidatorsEventuallyStore system trace commonSet k ∧
      let ⟨_, operations⟩ := trace k
      -- the common subset contains blocks from at least 2f + 1 validators in round r
      (authorsInCommonSet operations commonSet r).length ≥ 2 * system.f + 1


end BlockSynchroniser.Executions

---------------------------------------------------------------------
-- This namespace contains the operations that validators can perform.
---------------------------------------------------------------------
namespace BlockSynchroniser.Operations

-- Validator operation semantics
def canPropose (system : BlockSynchroniserSystem) (validatorId : ValidatorId) (block : Block) (state : SystemState) : Bool :=
  match getValidatorById state validatorId with
  | some _ =>
    block.author = validatorId &&
    block.r = state.currentRound &&
    isBlockValid system block state
  | none => false

def canAccept (_system : BlockSynchroniserSystem) (validatorId : ValidatorId) (_blockDigest : BlockDigest) (state : SystemState) : Bool :=
  match getValidatorById state validatorId with
  | some _ => true -- simplified for now
  | none => false

def canStore (system : BlockSynchroniserSystem) (validatorId : ValidatorId) (block : Block) (state : SystemState) : Bool :=
  match getValidatorById state validatorId with
  | some validator =>
    block.d ∈ validator.acceptedBlocks &&
    isBlockValid system block state
  | none => false

end BlockSynchroniser.Operations
