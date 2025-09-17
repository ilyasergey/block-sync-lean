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
  deriving Repr, BEq

-- Validator state
structure Validator where
  id : ValidatorId -- Immutable
  isHonest : Bool -- Immutable
  acceptedBlocks : List BlockDigest -- accepted block digests
  storedBlocks : List BlockDigest -- stored block digests
  deriving Repr, BEq

-- System state
structure SystemState where
  validators : List Validator
  blocks : List Block
  currentRound : Round
  k : Nat -- parameter for parent requirements
  deriving Repr

-- Operations that validators can perform
inductive ValidatorOperation where
  | block_propose (validatorId : ValidatorId) (block : Block) : ValidatorOperation
  | block_accept (validatorId : ValidatorId) (blockDigest : BlockDigest) : ValidatorOperation
  | block_store (validatorId : ValidatorId) (block : Block) : ValidatorOperation
  deriving Repr

-- Block synchroniser system
structure BlockSynchroniserSystem where
  n : Nat -- total number of validators
  f : Nat -- maximum number of Byzantine validators
  k : Nat -- minimum number of parent blocks required
  validators : List ValidatorId
  deriving Repr

-- Properties and invariants
def isByzantineValidator (v : Validator) : Bool := !v.isHonest

def isHonestValidator (v : Validator) : Bool := v.isHonest

def getValidatorById (state : SystemState) (id : ValidatorId) : Option Validator :=
  state.validators.find? (fun v => v.id = id)

def getBlockByDigest (state : SystemState) (digest : BlockDigest) : Option Block :=
  state.blocks.find? (fun b => b.d = digest)

-- Block validity conditions
def hasValidParents (block : Block) (state : SystemState) : Bool :=
  block.parents.length >= state.k &&
  block.parents.all (fun parentDigest =>
    match getBlockByDigest state parentDigest with
    | some parent => parent.r = block.r - 1
    | none => false)

-- Block validity conditions: non-empty, has valid parents
def isBlockValid (block : Block) (state : SystemState) : Bool :=
  block.r > 0 && -- non-empty, ever-growing
  hasValidParents block state

-- This invariant ensures that the number of Byzantine validators is at most f.
def atMostFByzantine (system : BlockSynchroniserSystem) (state : SystemState) : Bool :=
  let byzantineCount := state.validators.filter isByzantineValidator |>.length
  byzantineCount ≤ system.f

-- This invariant ensures that the number of Byzantine validators is at most f.
-- This is a necessary condition for the system to be able to tolerate f
-- Byzantine validators.
def allValidatorsPresent (system : BlockSynchroniserSystem) (state : SystemState) : Bool :=
  state.validators.length = system.n &&
  state.validators.all (fun v => v.id ∈ system.validators)

-- Main system invariant: at most f Byzantine validators, all validators
-- present, and all blocks valid.
def systemInvariant (system : BlockSynchroniserSystem) (state : SystemState) : Bool :=
  atMostFByzantine system state &&
  allValidatorsPresent system state &&
  state.blocks.all (fun b => isBlockValid b state)

end BlockSynchroniser



-- This namespace contains the operations that validators can perform.
namespace BlockSynchroniser.Operations

-- Validator operation semantics
def canPropose (validatorId : ValidatorId) (block : Block) (state : SystemState) : Bool :=
  match getValidatorById state validatorId with
  | some _ =>
    block.author = validatorId &&
    block.r = state.currentRound &&
    isBlockValid block state
  | none => false

def canAccept (validatorId : ValidatorId) (_blockDigest : BlockDigest) (state : SystemState) : Bool :=
  match getValidatorById state validatorId with
  | some _ => true -- simplified for now
  | none => false

def canStore (validatorId : ValidatorId) (block : Block) (state : SystemState) : Bool :=
  match getValidatorById state validatorId with
  | some validator =>
    block.d ∈ validator.acceptedBlocks &&
    isBlockValid block state
  | none => false

end BlockSynchroniser.Operations


namespace BlockSynchroniser.Execution

-- System state with pending operations
structure SystemSnapshot where
  state : SystemState
  pendingOperations : List ValidatorOperation
  deriving Repr

-- TODO: A system step relation determining the next valid snapshots



end BlockSynchroniser.Execution


-- Examples
namespace BlockSynchroniser.Examples

-- Example usage
def exampleSystem : BlockSynchroniserSystem := {
  n := 4,
  f := 1,
  k := 2,
  validators := [0, 1, 2, 3]
}

def exampleValidators : List Validator := [
  { id := 0, isHonest := true, acceptedBlocks := [], storedBlocks := [] },
  { id := 1, isHonest := true, acceptedBlocks := [], storedBlocks := [] },
  { id := 2, isHonest := false, acceptedBlocks := [], storedBlocks := [] },
  { id := 3, isHonest := true, acceptedBlocks := [], storedBlocks := [] }
]

def exampleState : SystemState := {
  validators := exampleValidators,
  blocks := [],
  currentRound := 1,
  k := 2
}

-- Example block creation
def createBlock (author : ValidatorId) (round : Round) (digest : BlockDigest) (parents : List BlockDigest) (payload : List Transaction) : Block := {
  r := round,
  author := author,
  d := digest,
  parents := parents,
  payload := payload
}

end BlockSynchroniser.Examples
