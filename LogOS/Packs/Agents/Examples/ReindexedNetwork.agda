{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Examples.ReindexedNetwork where

open import LogOS.Prelude
open import Data.Bool using (Bool; true; false)

open import LogOS.Base.Signature
open import LogOS.Base.Signature.Hom using (SigHom)
open import LogOS.Kernel.LogicKernel.Reindex using (reindexLogicKernel)
open import LogOS.Adapters.Views.SatMor using (satMor-reindexLogicKernel-boundary)

open import LogOS.Domain.Universality.Core using (ToyUCode; ToyC; mkC)
import LogOS.Domain.Universality.KernelRich as KR

open import LogOS.Free.ConstraintsOverSig using (Con∂; I∂; atom∂; rename∂)
import LogOS.Computation.SchemeCategory as Cat
import LogOS.Computation.KernelUniversalProcess as KUP
open import LogOS.Minimal.Adapter using (QAdapter)

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
open import LogOS.Packs.Agents.Socket.Ports using (AgentPorts)
open import LogOS.Packs.Agents.Socket.Contracts using (AgentContracts)
import LogOS.Packs.Agents.Socket.FromKernel as FromKernel
open import LogOS.Packs.Agents.Networks.Hetero using (AgentNode; AgentNetwork)
import LogOS.Packs.Agents.Networks.Interop as Interop

-- A tiny non-identity signature map into the UniversalIR toy signature.

SigBool : LogOSSignature lzero
SigBool = record
  { sorts = record
      { Iface = Bool
      ; Cosp = Bool
      ; ∂Cosp = Bool
      }
  ; cospanOps = record
      { src = λ _ → false
      ; tgt = λ _ → false
      ; idC = λ _ → false
      ; _∘C_ = λ _ _ → false
      ; _⊕C_ = λ _ _ → false
      ; _⊗C_ = λ _ _ → false
      }
  ; boundaryOps = record
      { src∂ = λ _ → false
      ; tgt∂ = λ _ → false
      ; id∂ = λ _ → false
      ; _∘∂_ = λ _ _ → false
      ; _⊕∂_ = λ _ _ → false
      ; _⊗∂_ = λ _ _ → false
      ; from∂ = λ _ → false
      ; to∂ = λ _ → false
      }
  }

σ : SigHom SigBool KR.Sig
σ = record
  { mapIface  = λ _ → tt
  ; mapCosp   = λ _ → tt
  ; map∂Cosp  = λ _ → tt
  ; src-pres  = λ _ → refl
  ; tgt-pres  = λ _ → refl
  ; idC-pres  = λ _ → refl
  ; ∘C-pres   = λ _ _ → refl
  ; ⊕C-pres   = λ _ _ → refl
  ; ⊗C-pres   = λ _ _ → refl
  ; src∂-pres = λ _ → refl
  ; tgt∂-pres = λ _ → refl
  ; id∂-pres  = λ _ → refl
  ; ∘∂-pres   = λ _ _ → refl
  ; ⊕∂-pres   = λ _ _ → refl
  ; ⊗∂-pres   = λ _ _ → refl
  ; from∂-pres = λ _ → refl
  ; to∂-pres   = λ _ → refl
  }

-- Overlap at the syntax level: two distinct interfaces collapse under `σ`.
-- Here `σ.mapIface` sends both `true` and `false` to the unique `⊤` interface.

atomF : Con∂ SigBool
atomF = atom∂ false

atomT : Con∂ SigBool
atomT = atom∂ true

overlap-rename : rename∂ σ atomF ≡ rename∂ σ atomT
overlap-rename = refl

Task : Set
Task = ⊤

defaultCon : ToyUCode
defaultCon = ToyC (mkC 0)

portsBool : AgentPorts SigBool
portsBool = record
  { Obs = false
  ; Act = false
  ; Reward = false
  ; Oversight = false
  ; Shutdown = false
  ; Comm = false
  }

portsUnit : AgentPorts KR.Sig
portsUnit = record
  { Obs = tt
  ; Act = tt
  ; Reward = tt
  ; Oversight = tt
  ; Shutdown = tt
  ; Comm = tt
  }

val∂Bool : Bool → ToyUCode
val∂Bool _ = defaultCon

val∂Unit : LogOSSignature.Iface KR.Sig → ToyUCode
val∂Unit _ = defaultCon

contractsBool : AgentContracts SigBool
contractsBool = record { Objective = I∂ ; Safety = I∂ ; Assumes = I∂ }

contractsUnit : AgentContracts KR.Sig
contractsUnit = record { Objective = I∂ ; Safety = I∂ ; Assumes = I∂ }

K₂ = KR.UKR
module SockUnit = FromKernel.For K₂ Task

LK₁ = reindexLogicKernel σ SockUnit.LK
module KPBool = KUP.ForLogicKernel LK₁ (QAdapter.e KR.Q)

choiceBool : Cat.Choice Task KPBool.BoundaryProcess
choiceBool = record { compile = λ _ → defaultCon ; fuel = λ _ → zero }

choiceUnit : Cat.Choice Task SockUnit.KP.BoundaryProcess
choiceUnit = record { compile = λ _ → defaultCon ; fuel = λ _ → zero }

socketBool : AgentSocket SigBool KR.Q Task
socketBool = record
  { LK     = LK₁
  ; ports  = portsBool
  ; val∂   = val∂Bool
  ; C      = contractsBool
  ; P      = KPBool.BoundaryProcess
  ; choice = choiceBool
  }
socketUnit = SockUnit.mkBoundarySocket portsUnit val∂Unit contractsUnit choiceUnit

module SemanticsOverlap where
  open AgentSocket socketUnit using (⟦_⟧)

  -- The collapse survives interpretation: the two renamed atoms denote the
  -- same boundary constraint in the target socket.
  overlap-sem : ⟦ rename∂ σ atomF ⟧ ≡ ⟦ rename∂ σ atomT ⟧
  overlap-sem = cong (λ c → ⟦ c ⟧) overlap-rename

nodeBool : AgentNode
nodeBool = record
  { Sig  = SigBool
  ; Q    = KR.Q
  ; Task = Task
  ; Sock = socketBool
  }

nodeUnit : AgentNode
nodeUnit = record
  { Sig  = KR.Sig
  ; Q    = KR.Q
  ; Task = Task
  ; Sock = socketUnit
  }

data Role : Set where
  left right : Role

network : AgentNetwork Role
network = record
  { node = λ where
      left  → nodeBool
      right → nodeUnit
  }

module Net = AgentNetwork network

edge : Net.Edge left right
edge = record
  { satMor = satMor-reindexLogicKernel-boundary σ SockUnit.LK }

portL = AgentSocket.canonicalBoundaryPort socketBool
portR = AgentSocket.canonicalBoundaryPort socketUnit

module LR = Interop.For network edge portL portR

translateLeftToRight : Net.Con left → Net.Con right
translateLeftToRight = LR.translate
