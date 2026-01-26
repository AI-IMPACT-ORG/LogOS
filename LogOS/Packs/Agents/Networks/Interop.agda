{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Networks.Interop where

open import LogOS.Prelude

open import LogOS.Boundary.Port using (BoundaryPort)
open import LogOS.Syntax.Prop as Prop
open import LogOS.Ports.Semantic.Interlingua using (toPresentationC)
open import LogOS.Ports.Semantic.PresentationCore using (PresentationC)
open import LogOS.Ports.Semantic.SystemIO using (SystemIO; SystemIO↑; rebaseAlongSatMor)
import LogOS.Ports.Semantic.HeteroInterlinguaCore as Hetero
import LogOS.Ports.Semantic.Interoperability as Interop
import LogOS.Ports.Semantic.SignaturePushoutHub as SigHub

open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
open import LogOS.Packs.Agents.Networks.Hetero using (AgentNetwork)
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Base.Signature.Hom using (SigSpan; SigPushout; SigCocone)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel.LogicKernel using (LogicKernel)
open import LogOS.Kernel.LogicKernel.Reindex using (reindexLogicKernel)
import LogOS.Kernel.LogicKernel.Boundary as LKBoundary

-- Heterogeneous interlingua for network edges (conservative/equivalence):
-- combine a SatMor edge with boundary ports to obtain canonical translations
-- between external formula languages.

module ForEquiv
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
    m = AgentNetwork.Edge.satMor edge

  module HR = Hetero.For m PR PS
  open HR public

  -- Edge adapters are heterogeneous port adapters over the edge SatMor.
  EdgeAdapter : Set _
  EdgeAdapter = Interop.HeteroPortAdapter m PR PS

  canonicalAdapter : EdgeAdapter
  canonicalAdapter = Interop.heteroCanonicalAdapter m PR PS

  adapter-unique
    : ∀ (A : EdgeAdapter)
    → HR._≈⇒_ (Interop.HeteroPortAdapter.map A) translate
  adapter-unique = Interop.heteroAdapter-unique m PR PS

  adapter-confluent
    : ∀ {A B : EdgeAdapter}
    → HR._≈⇒_ (Interop.HeteroPortAdapter.map A) (Interop.HeteroPortAdapter.map B)
  adapter-confluent {A} {B} = Interop.heteroAdapter-confluent m PR PS {A} {B}

  adapter-respects-ObsEq
    : ∀ (A : EdgeAdapter) {φ ψ}
    → PresentationC.ObsEqF PR φ ψ
    → ∀ p → Prop._↔_ (SatF₂↑ p (Interop.HeteroPortAdapter.map A φ))
                     (SatF₂↑ p (Interop.HeteroPortAdapter.map A ψ))
  adapter-respects-ObsEq A = Interop.heteroAdapter-respects-ObsEqF m PR PS A

  -- Tool rebasing along an edge (pullback along the edge SatMor).
  rebaseAlongEdge
    : ∀ {ℓName ℓFormS ℓWProver ℓWModel}
      {Name : Set ℓName}
    → SystemIO
        {ℓForm = ℓFormS}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name (Ctx s) (Con s) (Sat s)
    → SystemIO↑
        {ℓForm = ℓFormR}
        {ℓWProver = ℓWProver}
        {ℓWModel = ℓWModel}
        Name (Ctx r) (Con r) (Sat r)
  rebaseAlongEdge sys = rebaseAlongSatMor m PR sys

  -- -------------------------------------------------------------------------
  -- Limit/stabilisation transport across an edge (μ-level).
  --
  -- This strengthens “ported closure naturality” (one-step `Extend`) to a
  -- limit-level statement about exported Kleene μ fixed points on constraints.
  -- -------------------------------------------------------------------------

  module Limit where
    private
      CP₁ : ConPreorder ℓ
      CP₁ = ConPreorderAt r

      CP₂ : ConPreorder ℓ
      CP₂ = ConPreorderAt s

      module L = Interop.Limit CP₁ CP₂ m PR PS

    open L public using (MuTransportData; MuTransportData↑)

    translate-μ≤
      : ∀ {ω₁ : Truth.GuardedCore.OmegaCPO CP₁}
          {ω₂ : Truth.GuardedCore.OmegaCPO CP₂}
          {F₁ : Con r → Con r}
          {F₂ : Con s → Con s}
      → MuTransportData ω₁ ω₂ F₁ F₂
      → ∀ p
      → SatF₂↑ p (translate (BoundaryPort.Interp PortR (Truth.GuardedCore.Kleene.μ ω₁ F₁)))
      → SatF₂↑ p (BoundaryPort.Interp PortS (Truth.GuardedCore.Kleene.μ ω₂ F₂))
    translate-μ≤ = L.translate-μ≤

    translate-μ≤↑ = L.translate-μ≤↑

    translate-preserves-stabilisation≤ = translate-μ≤
    translate-preserves-stabilisation≤↑ = translate-μ≤↑

-- Sound-only interlingua for network edges (default):
-- a SatHom edge induces a canonical one-way translation between ports.

module For
  {ℓ ℓTask ℓRole : Level}
  {Role : Set ℓRole}
  (Net : AgentNetwork {ℓ} {ℓTask} Role)
  {r s : Role}
  (edge : AgentNetwork.EdgeSound Net r s)
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
    m = AgentNetwork.EdgeSound.satHom edge

  module HR = Hetero.ForSound m PR PS
  open HR public

  -- Edge refinements are heterogeneous port refinements over the edge SatHom.
  EdgeRefinement : Set _
  EdgeRefinement = Interop.HeteroPortRefinement m PR PS

  canonicalRefinement : EdgeRefinement
  canonicalRefinement = Interop.heteroCanonicalRefinement m PR PS

  refinement-correct
    : ∀ (A : EdgeRefinement) p φ
    → BoundaryPort.SatF PortR p φ
    → SatF₂↑ p (Interop.HeteroPortRefinement.map A φ)
  refinement-correct A = Interop.HeteroPortRefinement.preserves-Sat A

-- Pushout hub wiring for agent-facing ports (sound-only).
-- This is a convenience layer around the semantic hub module.

module PushoutHub
  {ℓ : Level}
  {Sig₀ Sig₁ Sig₂ : LogOSSignature ℓ}
  (span : SigSpan Sig₀ Sig₁ Sig₂)
  (po   : SigPushout span)
  {Q : QAdapter ℓ}
  (K : LogicKernel (SigPushout.SigP po) Q)
  {ℓFormL ℓFormR ℓFormP : Level}
  (PortL : BoundaryPort {ℓForm = ℓFormL} Sig₁ Q _ _ _
            (LKBoundary.boundaryIO (reindexLogicKernel (SigCocone.inl (SigPushout.cocone po)) K)))
  (PortR : BoundaryPort {ℓForm = ℓFormR} Sig₂ Q _ _ _
            (LKBoundary.boundaryIO (reindexLogicKernel (SigCocone.inr (SigPushout.cocone po)) K)))
  (PortP : BoundaryPort {ℓForm = ℓFormP} (SigPushout.SigP po) Q _ _ _
            (LKBoundary.boundaryIO K))
  where

  module Hub = SigHub.ForLogicKernel span po K
  open Hub.Ports PortL PortR PortP public
