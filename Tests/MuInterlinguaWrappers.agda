{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.MuInterlinguaWrappers where

-- Smoke test: ensure the μ-level wrapper APIs stay wired up.
--
-- This is intentionally polymorphic: it does not build a concrete instance,
-- it only checks that the wrapper names and their types remain available.

open import LogOS.Prelude

open import LogOS.Boundary.Port using (BoundaryPort)
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel using (Kernel)
import LogOS.Kernel.Boundary as KBoundary

import LogOS.Packs.Agents.Socket.Core as Sock
open import LogOS.Packs.Agents.Networks.Hetero using (AgentNetwork)
import LogOS.Packs.Agents.Networks.Interop as NetInterop
import LogOS.Packs.Agents.Networks.MonitorInterop as MonitorInterop

import LogOS.Ports.Semantic.InterlinguaCodeKernel as CodeKernel

module _
  {ℓ ℓTask ℓRole : Level}
  {Role : Set ℓRole}
  (Net : AgentNetwork {ℓ} {ℓTask} Role)
  {r s : Role}
  (edge : AgentNetwork.Edge Net r s)
  {ℓFormR ℓFormS : Level}
  (PortR : BoundaryPort {ℓForm = ℓFormR} _ _ _ _ _
           (Sock.AgentSocket.boundaryIO (AgentNetwork.Sock Net r)))
  (PortS : BoundaryPort {ℓForm = ℓFormS} _ _ _ _ _
           (Sock.AgentSocket.boundaryIO (AgentNetwork.Sock Net s)))
  where
  module E = NetInterop.ForEquiv Net edge PortR PortS
  open E.Limit

  private
    agent-translate-μ≤-exists : _
    agent-translate-μ≤-exists = translate-μ≤

module _
  {ℓ ℓTask ℓRole : Level}
  {Role : Set ℓRole}
  (Net : AgentNetwork {ℓ} {ℓTask} Role)
  {r s : Role}
  (edge : AgentNetwork.Edge Net r s)
  {ℓFormR ℓFormS : Level}
  (PortR : BoundaryPort {ℓForm = ℓFormR} _ _ _ _ _
           (Sock.AgentSocket.boundaryIO (AgentNetwork.Sock Net r)))
  (PortS : BoundaryPort {ℓForm = ℓFormS} _ _ _ _ _
           (Sock.AgentSocket.boundaryIO (AgentNetwork.Sock Net s)))
  where
  module M = MonitorInterop.For Net edge PortR PortS
  open M.LimitMu

  private
    monitor-translate-μ≤-exists : _
    monitor-translate-μ≤-exists = monitor-translate-μ≤

module _
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  {ℓForm : Level}
  (P : BoundaryPort {ℓForm = ℓForm} Sig Q (Kernel.HWorld K) (Kernel.BB K)
          (Kernel.HTruth K) (KBoundary.boundaryIO K))
  (ωBnd : Truth.GuardedCore.OmegaCPO (BulkBoundary.bnd (Kernel.BB K)))
  where
  module CK = CodeKernel.For K P
  module L  = CK.Limit ωBnd

  private
    compile-μ≤-exists : _
    compile-μ≤-exists = L.compile-μ≤

    mkMuTransportData-exists : _
    mkMuTransportData-exists = L.mkMuTransportData

