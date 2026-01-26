{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Examples.HelloNetwork where

open import LogOS.Prelude

open import LogOS.Ports.Semantic.SatMor using (SatMor; idSatMor)
open import LogOS.Syntax.Prop as Prop

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
open import LogOS.Packs.Agents.Networks.Hetero using (AgentNode; AgentNetwork)
import LogOS.Packs.Agents.Networks.Interop as Interop
import LogOS.Packs.Agents.Networks.NetworkAgent as NetworkAgent

-- Minimal heterogeneous network wiring:
-- two roles, two (possibly different) sockets, plus a single SatMor edge.

module For
  {ℓ ℓTask : Level}
  (nodeL nodeR : AgentNode {ℓ} {ℓTask})
  where

  data Role : Set where
    left right : Role

  network : AgentNetwork Role
  network = record
    { node = λ where
        left  → nodeL
        right → nodeR
    }

  module Net = AgentNetwork network

  module WithEdge
    (edgeLRMor : SatMor (Net.Ctx left) (Net.Con left) (Net.Sat left)
                         (Net.Ctx right) (Net.Con right) (Net.Sat right))
    where

    edgeLR : Net.Edge left right
    edgeLR = record { satMor = edgeLRMor }

    -- Example: apply the edge wiring to update the right role's policy.
    edgeUpdateRight : Net.Policy → Net.Con right
    edgeUpdateRight pol = Net.edgeUpdate edgeLR pol

  module WithEdgeAndPorts
    (edgeLRMor : SatMor (Net.Ctx left) (Net.Con left) (Net.Sat left)
                         (Net.Ctx right) (Net.Con right) (Net.Sat right))
    where

    edgeLR : Net.Edge left right
    edgeLR = record { satMor = edgeLRMor }

    portL = AgentSocket.canonicalBoundaryPort (Net.Sock left)
    portR = AgentSocket.canonicalBoundaryPort (Net.Sock right)

    module LR = Interop.ForEquiv network edgeLR portL portR

    -- Canonical edge translation on formulas (here: boundary constraints).
    translateLeftToRight : Net.Con left → Net.Con right
    translateLeftToRight = LR.translate

module SameNode
  {ℓ ℓTask : Level}
  (node : AgentNode {ℓ} {ℓTask})
  where

  module Base = For node node
  open Base

  -- Explicit SatMor instantiation: identity edge on a shared node.
  edgeId : SatMor (Net.Ctx left) (Net.Con left) (Net.Sat left)
                  (Net.Ctx right) (Net.Con right) (Net.Sat right)
  edgeId = idSatMor (Net.Sat left)

  module Demo = WithEdge edgeId
  module DemoPorts = WithEdgeAndPorts edgeId

  module AsAgent where
    edgeToHub : (r : Role) → Net.Edge r left
    edgeToHub left  = record { satMor = idSatMor (Net.Sat left) }
    edgeToHub right = record { satMor = idSatMor (Net.Sat right) }

    aggregate : (Role → Net.Con left) → Net.Con left
    aggregate f = f left

    aggregate-respects-obsEq
      : ∀ {f g}
      → (∀ r → Prop.ObsEqOn (Net.Sat left) (f r) (g r))
      → Prop.ObsEqOn (Net.Sat left) (aggregate f) (aggregate g)
    aggregate-respects-obsEq eq = eq left

    netAgent : NetworkAgent.NetworkAgent Role
    netAgent = record
      { Net       = network
      ; hub       = left
      ; edgeToHub = edgeToHub
      ; aggregate = aggregate
      ; aggregate-respects-obsEq = aggregate-respects-obsEq
      }

    module NA = NetworkAgent.NetworkAgent netAgent

    networkSocket : AgentSocket (NA.Sig left) (NA.Q left) (NA.Task left)
    networkSocket = NA.socket
