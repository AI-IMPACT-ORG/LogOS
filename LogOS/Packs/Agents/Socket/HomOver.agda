{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Socket.HomOver where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Kernel.LogicKernel using (LogicKernel)
open import LogOS.Kernel.LogicKernel.HomOverSig as LKHomOver
open import LogOS.Kernel.LogicKernel.Reindex using (reindexLogicKernel)
import LogOS.Adapters.Views.SatMor as SatMorAdapters
open import LogOS.Ports.Semantic.SatMor using (SatMor)

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)

-- Logic-kernel homs between sockets (same Q) induce boundary satisfaction morphisms.

record HomEdge
  {ℓ ℓTask₁ ℓTask₂ : Level}
  {Sig₁ Sig₂ : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  {Task₁ : Set ℓTask₁}
  {Task₂ : Set ℓTask₂}
  (Sock₁ : AgentSocket Sig₁ Q Task₁)
  (Sock₂ : AgentSocket Sig₂ Q Task₂)
  : Set (lsuc (lsuc (ℓ ⊔ ℓTask₁ ⊔ ℓTask₂))) where
  field
    hom : LKHomOver.LogicKernelHomOver (AgentSocket.LK Sock₁) (AgentSocket.LK Sock₂)
    sat : SatMorAdapters.LogicKernelHomBoundarySat
            (AgentSocket.LK Sock₁)
            (reindexLogicKernel (LKHomOver.LogicKernelHomOver.σ hom) (AgentSocket.LK Sock₂))
            (LKHomOver.LogicKernelHomOver.hom hom)

toSatMor
  : ∀ {ℓ ℓTask₁ ℓTask₂ : Level}
    {Sig₁ Sig₂ : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {Task₁ : Set ℓTask₁}
    {Task₂ : Set ℓTask₂}
    {Sock₁ : AgentSocket Sig₁ Q Task₁}
    {Sock₂ : AgentSocket Sig₂ Q Task₂}
  → HomEdge Sock₁ Sock₂
  → let BB₁ = LogicKernel.BB (AgentSocket.LK Sock₁)
        BB₂ = LogicKernel.BB (AgentSocket.LK Sock₂)
    in SatMor (LogOSSignature.∂Cosp Sig₁) (BulkBoundary.Con_bnd BB₁) (LogicKernel.Sat_H_bnd (AgentSocket.LK Sock₁))
             (LogOSSignature.∂Cosp Sig₂) (BulkBoundary.Con_bnd BB₂) (LogicKernel.Sat_H_bnd (AgentSocket.LK Sock₂))
toSatMor h =
  SatMorAdapters.satMor-of-LogicKernelHomOver-boundary
    (HomEdge.hom h)
    (HomEdge.sat h)
