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

import BlockSynchroniser.Definitions

namespace DAGCertified

open BlockSynchroniser
open SystemState
open Properties

-- Additional operations specific to DAG-based certified protocol
inductive DAGCertifiedOperation where
  | signBlock (validatorId : ValidatorId) (blockDigest : BlockDigest) : DAGCertifiedOperation
  | broadcastCertificate (validatorId : ValidatorId) (blockDigest : BlockDigest) (signers : List ValidatorId) : DAGCertifiedOperation
  | requestMissingBlock (requesterId : ValidatorId) (blockDigest : BlockDigest) : DAGCertifiedOperation
  | provideMissingBlock (providerId : ValidatorId) (requesterId : ValidatorId) (block : Block) : DAGCertifiedOperation
  deriving Repr

-- DAG-based certified synchroniser protocol state
structure DAGCertifiedState where
  validators : List (ValidatorId × Validator) -- mapping from ID to validator state
  blocks : List Block -- all blocks seen in the system
  emittedOperations : List ValidatorOperation -- operations always remain available
  -- Additional state for DAG-based certified protocol
  certificates : List (BlockDigest × List ValidatorId) -- block digest to list of signers
  pendingBlocks : List Block -- blocks cached but not yet certified
  -- Track DAG-specific operations
  dagOperations : List DAGCertifiedOperation -- DAG-specific operations
  -- Track pending requests and responses for pull protocol
  pendingRequests : List (ValidatorId × BlockDigest) -- (requesterId, blockDigest)
  pendingProvisions : List (ValidatorId × ValidatorId × Block) -- (providerId, requesterId, block)
  -- Track per-validator rounds for DAG protocol
  validatorRounds : List (ValidatorId × Round) -- current round for each validator
  deriving Repr

-- Instance of SystemState type class for DAG-based certified protocol
instance : SystemState DAGCertifiedState where
  validators s := s.validators
  blocks s := s.blocks
  emittedOperations s := s.emittedOperations

-- Helper functions for DAG-based certified protocol

-- Check if a block has a certificate with at least 2f+1 signatures
def hasCertificate (system : BlockSynchroniserSystem) (state : DAGCertifiedState)
    (blockDigest : BlockDigest) : Bool :=
  match state.certificates.find? (fun (d, _) => d = blockDigest) with
  | some (_, signers) => signers.length ≥ 2 * system.f + 1
  | none => false

-- Get signers of a block's certificate
def getCertificateSigners (state : DAGCertifiedState) (blockDigest : BlockDigest)
    : Option (List ValidatorId) :=
  state.certificates.find? (fun (d, _) => d = blockDigest) |>.map (fun (_, signers) => signers)

-- Check if a block is in pending state (cached but not certified)
def isPendingBlock (state : DAGCertifiedState) (blockDigest : BlockDigest) : Bool :=
  state.pendingBlocks.any (fun b => b.d = blockDigest)

-- Union type for all operations in DAG-based certified protocol
inductive DAGCertifiedTransitionOp where
  | basicOp (op : ValidatorOperation) : DAGCertifiedTransitionOp
  | dagOp (op : DAGCertifiedOperation) : DAGCertifiedTransitionOp
  deriving Repr

open ValidatorOperation
open DAGCertifiedOperation
open DAGCertifiedTransitionOp

variable (system: BlockSynchroniserSystem)

-- Transition relation for DAG-based certified synchroniser protocol
inductive DAGCertifiedTransition :
  DAGCertifiedState → DAGCertifiedTransitionOp → DAGCertifiedState → Prop

-- TODO: implement the protocol


end DAGCertified
