{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Networks.Hetero where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.Ports.Semantic.SatMor using (SatMor)
open import LogOS.Algebra.ConAlg using (ConAlg)

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)

-- Heterogeneous agent networks: each role may carry its own signature/kernel.
-- Wiring is expressed via satisfaction morphisms between boundary interfaces.
--
-- `Edge` uses `SatMor`, which preserves *and reflects* satisfaction. This makes
-- the edge a conservative translation rather than a one-way sound abstraction.

record AgentNode {ℓ ℓTask : Level} : Set (lsuc (lsuc (ℓ ⊔ ℓTask))) where
  field
    Sig  : LogOSSignature ℓ
    Q    : QAdapter ℓ
    Task : Set ℓTask
    Sock : AgentSocket Sig Q Task

  -- Re-export the socket surface for convenience.
  open AgentSocket Sock public

record AgentNetwork {ℓ ℓTask ℓRole : Level} (Role : Set ℓRole)
  : Set (lsuc (lsuc (ℓ ⊔ ℓTask ⊔ ℓRole))) where

  field
    node : Role → AgentNode {ℓ} {ℓTask}

  -- Per-role accessors.
  Sig : Role → LogOSSignature ℓ
  Sig r = AgentNode.Sig (node r)

  Q : Role → QAdapter ℓ
  Q r = AgentNode.Q (node r)

  Task : Role → Set ℓTask
  Task r = AgentNode.Task (node r)

  Sock : (r : Role) → AgentSocket (Sig r) (Q r) (Task r)
  Sock r = AgentNode.Sock (node r)

  -- Boundary interface per role.
  Ctx : Role → Set ℓ
  Ctx r = LogOSSignature.∂Cosp (Sig r)

  Con : Role → Set ℓ
  Con r = let open AgentSocket (Sock r) in Con_bnd

  Sat : (r : Role) → Ctx r → Con r → Set ℓ
  Sat r = BoundaryIO.Sat∂ (AgentSocket.boundaryIO (Sock r))

  conAlg : (r : Role) → ConAlg {ℓ}
  conAlg r = AgentSocket.conAlg (Sock r)

  tensorAt : (r : Role) → Con r → Con r → Con r
  tensorAt r c d = ConAlg._⊗∂_ (conAlg r) c d

  -- A policy is a role-indexed assignment of boundary constraints.
  Policy : Set (ℓ ⊔ ℓRole)
  Policy = (r : Role) → Con r

  -- Edge wiring: a conservative translation between boundary satisfactions.
  record Edge (r s : Role) : Set (lsuc (ℓ ⊔ ℓRole)) where
    field
      satMor : SatMor (Ctx r) (Con r) (Sat r)
                       (Ctx s) (Con s) (Sat s)

    translateCon : Con r → Con s
    translateCon = SatMor.mapCon satMor

  edgeTensor : ∀ {r s} → Edge r s → Con s → Con r → Con s
  edgeTensor {r} {s} e cₛ cᵣ =
    tensorAt s cₛ (Edge.translateCon e cᵣ)

  edgeUpdate : ∀ {r s} → Edge r s → Policy → Con s
  edgeUpdate {r} {s} e pol = edgeTensor e (pol s) (pol r)
