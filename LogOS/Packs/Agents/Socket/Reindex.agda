{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Socket.Reindex where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Base.Signature.Hom using (SigHom)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.ConstraintsOverSig using (rename∂)
open import LogOS.Boundary.Port using (BoundaryPort)
open import LogOS.Ports.Semantic.Interlingua using (toPresentationC)
import LogOS.Ports.Semantic.Interoperability as Interop
open import LogOS.Kernel using (Kernel)
open import LogOS.Kernel.Reindex using (reindexKernel)
import LogOS.Boundary.FromKernel as LKBoundary
import LogOS.Adapters.Views.SatMor as SatMorAdapters
open import LogOS.Ports.Semantic.SatMor using (SatMor)
open import LogOS.Ports.Semantic.Core using (boundarySatSystem)

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
open import LogOS.Packs.Agents.Socket.Ports using (AgentPorts)
open import LogOS.Packs.Agents.Socket.Contracts using (AgentContracts)

-- Push ports/contracts forward along a signature map.

renamePorts
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ}
    (σ : SigHom Sig₁ Sig₂)
  → AgentPorts Sig₁ → AgentPorts Sig₂
renamePorts σ ports =
  record
    { Obs       = SigHom.mapIface σ (AgentPorts.Obs ports)
    ; Act       = SigHom.mapIface σ (AgentPorts.Act ports)
    ; Reward    = SigHom.mapIface σ (AgentPorts.Reward ports)
    ; Oversight = SigHom.mapIface σ (AgentPorts.Oversight ports)
    ; Shutdown  = SigHom.mapIface σ (AgentPorts.Shutdown ports)
    ; Comm      = SigHom.mapIface σ (AgentPorts.Comm ports)
    }

renameContracts
  : ∀ {ℓ : Level} {Sig₁ Sig₂ : LogOSSignature ℓ}
    (σ : SigHom Sig₁ Sig₂)
  → AgentContracts Sig₁ → AgentContracts Sig₂
renameContracts σ C =
  record
    { Objective = rename∂ σ (AgentContracts.Objective C)
    ; Safety    = rename∂ σ (AgentContracts.Safety C)
    ; Assumes   = rename∂ σ (AgentContracts.Assumes C)
    }

-- Pull back a socket along a signature map, keeping the process/choice intact.
-- Ports and contracts must be supplied for the source signature.

reindexSocket
  : ∀ {ℓ ℓTask : Level}
    {Sig₁ Sig₂ : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    {Task : Set ℓTask}
  → AgentSocket Sig₂ Q Task
  → AgentPorts Sig₁
  → AgentContracts Sig₁
  → AgentSocket Sig₁ Q Task
reindexSocket σ Sock ports₁ C₁ =
  record
    { LK     = reindexKernel σ (AgentSocket.LK Sock)
    ; ports  = ports₁
    ; val∂   = λ a → AgentSocket.val∂ Sock (SigHom.mapIface σ a)
    ; C      = C₁
    ; P      = AgentSocket.P Sock
    ; interface = AgentSocket.interface Sock
    }

-- Canonical boundary satisfaction morphism induced by reindexing.

reindexSocketSatMor
  : ∀ {ℓ ℓTask : Level}
    {Sig₁ Sig₂ : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    {Task : Set ℓTask}
    (Sock : AgentSocket Sig₂ Q Task)
  → let
      BB = Kernel.BB (AgentSocket.LK Sock)
      open BulkBoundary BB
    in SatMor
        (boundarySatSystem {Sig = Sig₁} {BB = BB}
          (Kernel.Sat_H_bnd (reindexKernel σ (AgentSocket.LK Sock))))
        (boundarySatSystem {Sig = Sig₂} {BB = BB}
          (Kernel.Sat_H_bnd (AgentSocket.LK Sock)))
reindexSocketSatMor σ Sock =
  SatMorAdapters.satMor-reindexKernel-boundary σ (AgentSocket.LK Sock)

-- Canonical port adapter for boundary ports across a signature reindex.
--
-- This packages the reindexing SatMor together with the port-level interlingua
-- tooling so downstream code can reuse adapter lemmas directly.

reindexPortAdapter
  : ∀ {ℓ ℓTask : Level}
    {Sig₁ Sig₂ : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    {Task : Set ℓTask}
    (Sock : AgentSocket Sig₂ Q Task)
    {ℓForm₁ ℓForm₂ : Level}
    (Port₁ : BoundaryPort {ℓForm = ℓForm₁} Sig₁ Q _ _ _
              (LKBoundary.boundaryIO (reindexKernel σ (AgentSocket.LK Sock))))
    (Port₂ : BoundaryPort {ℓForm = ℓForm₂} Sig₂ Q _ _ _
              (AgentSocket.boundaryIO Sock))
  → let
      B₁ = LKBoundary.boundaryIO (reindexKernel σ (AgentSocket.LK Sock))
      B₂ = AgentSocket.boundaryIO Sock
    in Interop.HeteroPortAdapter (reindexSocketSatMor σ Sock)
         (toPresentationC B₁ Port₁)
         (toPresentationC B₂ Port₂)
reindexPortAdapter σ Sock Port₁ Port₂ =
  let
    B₁ = LKBoundary.boundaryIO (reindexKernel σ (AgentSocket.LK Sock))
    B₂ = AgentSocket.boundaryIO Sock
  in
  Interop.heteroCanonicalAdapter (reindexSocketSatMor σ Sock)
    (toPresentationC B₁ Port₁)
    (toPresentationC B₂ Port₂)
