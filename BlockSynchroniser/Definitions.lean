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
  (base : P system (trace 0))
  (step : forall i, P system (trace i) → P system (trace (i + 1))) :
  forall i, P system (trace i) :=
  fun i => Nat.rec base (fun i ih => step i ih) i

---------------------------------------------------------------------
-- Properties of block synchroniser system
---------------------------------------------------------------------

-- Validity: If an honest validator V_i invokes block_propose_i(B,r), then every
-- honest validator eventually outputs block_accept(B.d)
def blockSynchroniserValidity system (trace: Trace) :=
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
        operations'[o']? = some (.block_accept vid' block.d)



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
