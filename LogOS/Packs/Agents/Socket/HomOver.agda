{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Socket.HomOver where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Kernel using (Kernel)
open import LogOS.Kernel.HomOverSig as LKHomOver
open import LogOS.Kernel.Reindex using (reindexKernel)
import LogOS.Adapters.Views.SatMor as SatMorAdapters
open import LogOS.Ports.Semantic.SatMor using (SatMor)
open import LogOS.Ports.Semantic.Core using (boundarySatSystem)

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
    hom : LKHomOver.KernelHomOver (AgentSocket.LK Sock₁) (AgentSocket.LK Sock₂)
    sat : SatMorAdapters.KernelHomBoundarySat
            (AgentSocket.LK Sock₁)
            (reindexKernel (LKHomOver.KernelHomOver.σ hom) (AgentSocket.LK Sock₂))
            (LKHomOver.KernelHomOver.hom hom)

toSatMor
  : ∀ {ℓ ℓTask₁ ℓTask₂ : Level}
    {Sig₁ Sig₂ : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {Task₁ : Set ℓTask₁}
    {Task₂ : Set ℓTask₂}
    {Sock₁ : AgentSocket Sig₁ Q Task₁}
    {Sock₂ : AgentSocket Sig₂ Q Task₂}
  → HomEdge Sock₁ Sock₂
  → let
      BB₁ = Kernel.BB (AgentSocket.LK Sock₁)
      BB₂ = Kernel.BB (AgentSocket.LK Sock₂)
    in SatMor
        (boundarySatSystem {Sig = Sig₁} {BB = BB₁} (Kernel.Sat_H_bnd (AgentSocket.LK Sock₁)))
        (boundarySatSystem {Sig = Sig₂} {BB = BB₂} (Kernel.Sat_H_bnd (AgentSocket.LK Sock₂)))
toSatMor h =
  SatMorAdapters.satMor-of-KernelHomOver-boundary
    (HomEdge.hom h)
    (HomEdge.sat h)
