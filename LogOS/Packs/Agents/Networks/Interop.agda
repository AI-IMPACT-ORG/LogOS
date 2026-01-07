{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Networks.Interop where

open import LogOS.Prelude

open import LogOS.Boundary.Port using (BoundaryPort)
open import LogOS.Ports.Semantic.Interlingua using (toPresentationC)
import LogOS.Ports.Semantic.HeteroInterlinguaCore as Hetero

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
open import LogOS.Packs.Agents.Networks.Hetero using (AgentNetwork)

-- Heterogeneous interlingua for network edges:
-- combine a SatMor edge with boundary ports to obtain canonical translations
-- between external formula languages.

module For
  {ℓ ℓTask ℓRole : Level}
  {Role : Set ℓRole}
  (Net : AgentNetwork {ℓ} {ℓTask} Role)
  {r s : Role}
  (edge : AgentNetwork.Edge Net r s)
  {ℓFormR ℓFormS : Level}
  (PortR : BoundaryPort {ℓForm = ℓFormR} _ _ _ _ _
           (AgentSocket.boundaryIO (AgentNetwork.Sock Net r)))
  (PortS : BoundaryPort {ℓForm = ℓFormS} _ _ _ _ _
           (AgentSocket.boundaryIO (AgentNetwork.Sock Net s)))
  where

  open AgentNetwork Net

  private
    SockR = Sock r
    SockS = Sock s

    PR = toPresentationC (AgentSocket.boundaryIO SockR) PortR
    PS = toPresentationC (AgentSocket.boundaryIO SockS) PortS

  module HR = Hetero.For (AgentNetwork.Edge.satMor edge) PR PS
  open HR public
