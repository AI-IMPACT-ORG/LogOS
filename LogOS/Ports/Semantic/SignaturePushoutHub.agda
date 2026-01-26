{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.SignaturePushoutHub where

-- Pushout-driven hub wiring for ports and tools.
--
-- The hub signature is the pushout; a hub kernel provides semantics there.
-- Branch kernels are obtained by reindexing along the cocone maps, yielding
-- canonical SatHom edges and port refinements into the hub.
--
-- The default interface is one-directional (sound-only). Equivalence-based
-- adapters live under the `*Equiv` modules.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Base.Signature.Hom
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.World
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.Boundary.Port using (BoundaryPort)

open import LogOS.Ports.Semantic.Interlingua using (toPresentationC)
open import LogOS.Ports.Semantic.PresentationCore using (PresentationC)
open import LogOS.Ports.Semantic.SatMor using (SatMor; SatHom; satHom-fromSatMor; idSatHom)
open import LogOS.Ports.Semantic.SystemIO using (SystemIO; SystemIO↑)
import LogOS.Ports.Semantic.BoundarySystemIO as BoundarySystemIO
import LogOS.Ports.Semantic.Interoperability as Interop
open import LogOS.Syntax.Prop as Prop

open import LogOS.Kernel
import LogOS.Kernel.Boundary as KBoundary
open import LogOS.Kernel.Reindex using (reindexKernel)
open import LogOS.Kernel.LogicKernel
import LogOS.Kernel.LogicKernel.Boundary as LKBoundary
open import LogOS.Kernel.LogicKernel.Reindex using (reindexLogicKernel)

open import LogOS.Adapters.Views.SatMor using
  ( satMor-reindexKernel-boundary
  ; satMor-reindexLogicKernel-boundary
  )

-- Conservative (⇔) variant: use when you explicitly want equivalence adapters.
module ForKernelEquiv
  {ℓ : Level}
  {Sig₀ Sig₁ Sig₂ : LogOSSignature ℓ}
  (span : SigSpan Sig₀ Sig₁ Sig₂)
  (po   : SigPushout span)
  {Q : QAdapter ℓ}
  (K : Kernel (SigPushout.SigP po) Q)
  where

  open SigPushout po renaming (SigP to SigP; cocone to cocone)
  open SigCocone cocone renaming (inl to inl; inr to inr)

  K₁ : Kernel Sig₁ Q
  K₁ = reindexKernel inl K

  K₂ : Kernel Sig₂ Q
  K₂ = reindexKernel inr K

  Bp : BoundaryIO SigP Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K)
  Bp = KBoundary.boundaryIO K

  B₁ : BoundaryIO Sig₁ Q (Kernel.HWorld K₁) (Kernel.BB K₁) (Kernel.HTruth K₁)
  B₁ = KBoundary.boundaryIO K₁

  B₂ : BoundaryIO Sig₂ Q (Kernel.HWorld K₂) (Kernel.BB K₂) (Kernel.HTruth K₂)
  B₂ = KBoundary.boundaryIO K₂

  satMorL
    : SatMor (LogOSSignature.∂Cosp Sig₁) (BulkBoundary.Con_bnd (Kernel.BB K₁))
             (BoundaryIO.Sat∂ B₁)
             (LogOSSignature.∂Cosp SigP) (BulkBoundary.Con_bnd (Kernel.BB K))
             (BoundaryIO.Sat∂ Bp)
  satMorL = satMor-reindexKernel-boundary inl K

  satMorR
    : SatMor (LogOSSignature.∂Cosp Sig₂) (BulkBoundary.Con_bnd (Kernel.BB K₂))
             (BoundaryIO.Sat∂ B₂)
             (LogOSSignature.∂Cosp SigP) (BulkBoundary.Con_bnd (Kernel.BB K))
             (BoundaryIO.Sat∂ Bp)
  satMorR = satMor-reindexKernel-boundary inr K

  module Ports
    {ℓFormL ℓFormR ℓFormP : Level}
    (PL : BoundaryPort {ℓForm = ℓFormL} Sig₁ Q _ _ _ B₁)
    (PR : BoundaryPort {ℓForm = ℓFormR} Sig₂ Q _ _ _ B₂)
    (PP : BoundaryPort {ℓForm = ℓFormP} SigP Q _ _ _ Bp)
    where

    P₁ = toPresentationC B₁ PL
    P₂ = toPresentationC B₂ PR
    Ph = toPresentationC Bp PP

    LeftToHub : Interop.HeteroPortAdapter satMorL P₁ Ph
    LeftToHub = Interop.heteroCanonicalAdapter satMorL P₁ Ph

    RightToHub : Interop.HeteroPortAdapter satMorR P₂ Ph
    RightToHub = Interop.heteroCanonicalAdapter satMorR P₂ Ph

    mapL : BoundaryPort.Form PL → BoundaryPort.Form PP
    mapL = Interop.HeteroPortAdapter.map LeftToHub

    mapR : BoundaryPort.Form PR → BoundaryPort.Form PP
    mapR = Interop.HeteroPortAdapter.map RightToHub

    ObsEqViaHub
      : BoundaryPort.Form PL → BoundaryPort.Form PR → Set _
    ObsEqViaHub φ ψ = PresentationC.ObsEqF Ph (mapL φ) (mapR ψ)

    rebaseHubToLeft
      : ∀ {ℓName ℓWProver ℓWModel}
        {Name : Set ℓName}
      → SystemIO
          {ℓForm = ℓFormP}
          {ℓWProver = ℓWProver}
          {ℓWModel = ℓWModel}
          Name (LogOSSignature.∂Cosp SigP)
          (BulkBoundary.Con_bnd (Kernel.BB K))
          (BoundaryIO.Sat∂ Bp)
      → SystemIO↑
          {ℓForm = ℓFormL}
          {ℓWProver = ℓWProver}
          {ℓWModel = ℓWModel}
          Name (LogOSSignature.∂Cosp Sig₁)
          (BulkBoundary.Con_bnd (Kernel.BB K₁))
          (BoundaryIO.Sat∂ B₁)
    rebaseHubToLeft sys =
      BoundarySystemIO.rebaseAlongSatMorToBoundaryPort B₁ PL {B₂ = Bp} satMorL sys

    rebaseHubToRight
      : ∀ {ℓName ℓWProver ℓWModel}
        {Name : Set ℓName}
      → SystemIO
          {ℓForm = ℓFormP}
          {ℓWProver = ℓWProver}
          {ℓWModel = ℓWModel}
          Name (LogOSSignature.∂Cosp SigP)
          (BulkBoundary.Con_bnd (Kernel.BB K))
          (BoundaryIO.Sat∂ Bp)
      → SystemIO↑
          {ℓForm = ℓFormR}
          {ℓWProver = ℓWProver}
          {ℓWModel = ℓWModel}
          Name (LogOSSignature.∂Cosp Sig₂)
          (BulkBoundary.Con_bnd (Kernel.BB K₂))
          (BoundaryIO.Sat∂ B₂)
    rebaseHubToRight sys =
      BoundarySystemIO.rebaseAlongSatMorToBoundaryPort B₂ PR {B₂ = Bp} satMorR sys

-- Conservative (⇔) variant: use when you explicitly want equivalence adapters.
module ForLogicKernelEquiv
  {ℓ : Level}
  {Sig₀ Sig₁ Sig₂ : LogOSSignature ℓ}
  (span : SigSpan Sig₀ Sig₁ Sig₂)
  (po   : SigPushout span)
  {Q : QAdapter ℓ}
  (K : LogicKernel (SigPushout.SigP po) Q)
  where

  open SigPushout po renaming (SigP to SigP; cocone to cocone)
  open SigCocone cocone renaming (inl to inl; inr to inr)

  K₁ : LogicKernel Sig₁ Q
  K₁ = reindexLogicKernel inl K

  K₂ : LogicKernel Sig₂ Q
  K₂ = reindexLogicKernel inr K

  Bp : BoundaryIO SigP Q (LogicKernel.HWorld K) (LogicKernel.BB K) (LogicKernel.HTruth K)
  Bp = LKBoundary.boundaryIO K

  B₁ : BoundaryIO Sig₁ Q (LogicKernel.HWorld K₁) (LogicKernel.BB K₁) (LogicKernel.HTruth K₁)
  B₁ = LKBoundary.boundaryIO K₁

  B₂ : BoundaryIO Sig₂ Q (LogicKernel.HWorld K₂) (LogicKernel.BB K₂) (LogicKernel.HTruth K₂)
  B₂ = LKBoundary.boundaryIO K₂

  satMorL
    : SatMor (LogOSSignature.∂Cosp Sig₁) (BulkBoundary.Con_bnd (LogicKernel.BB K₁))
             (BoundaryIO.Sat∂ B₁)
             (LogOSSignature.∂Cosp SigP) (BulkBoundary.Con_bnd (LogicKernel.BB K))
             (BoundaryIO.Sat∂ Bp)
  satMorL = satMor-reindexLogicKernel-boundary inl K

  satMorR
    : SatMor (LogOSSignature.∂Cosp Sig₂) (BulkBoundary.Con_bnd (LogicKernel.BB K₂))
             (BoundaryIO.Sat∂ B₂)
             (LogOSSignature.∂Cosp SigP) (BulkBoundary.Con_bnd (LogicKernel.BB K))
             (BoundaryIO.Sat∂ Bp)
  satMorR = satMor-reindexLogicKernel-boundary inr K

  module Ports
    {ℓFormL ℓFormR ℓFormP : Level}
    (PL : BoundaryPort {ℓForm = ℓFormL} Sig₁ Q _ _ _ B₁)
    (PR : BoundaryPort {ℓForm = ℓFormR} Sig₂ Q _ _ _ B₂)
    (PP : BoundaryPort {ℓForm = ℓFormP} SigP Q _ _ _ Bp)
    where

    P₁ = toPresentationC B₁ PL
    P₂ = toPresentationC B₂ PR
    Ph = toPresentationC Bp PP

    LeftToHub : Interop.HeteroPortAdapter satMorL P₁ Ph
    LeftToHub = Interop.heteroCanonicalAdapter satMorL P₁ Ph

    RightToHub : Interop.HeteroPortAdapter satMorR P₂ Ph
    RightToHub = Interop.heteroCanonicalAdapter satMorR P₂ Ph

    mapL : BoundaryPort.Form PL → BoundaryPort.Form PP
    mapL = Interop.HeteroPortAdapter.map LeftToHub

    mapR : BoundaryPort.Form PR → BoundaryPort.Form PP
    mapR = Interop.HeteroPortAdapter.map RightToHub

    ObsEqViaHub
      : BoundaryPort.Form PL → BoundaryPort.Form PR → Set _
    ObsEqViaHub φ ψ = PresentationC.ObsEqF Ph (mapL φ) (mapR ψ)

    rebaseHubToLeft
      : ∀ {ℓName ℓWProver ℓWModel}
        {Name : Set ℓName}
      → SystemIO
          {ℓForm = ℓFormP}
          {ℓWProver = ℓWProver}
          {ℓWModel = ℓWModel}
          Name (LogOSSignature.∂Cosp SigP)
          (BulkBoundary.Con_bnd (LogicKernel.BB K))
          (BoundaryIO.Sat∂ Bp)
      → SystemIO↑
          {ℓForm = ℓFormL}
          {ℓWProver = ℓWProver}
          {ℓWModel = ℓWModel}
          Name (LogOSSignature.∂Cosp Sig₁)
          (BulkBoundary.Con_bnd (LogicKernel.BB K₁))
          (BoundaryIO.Sat∂ B₁)
    rebaseHubToLeft sys =
      BoundarySystemIO.rebaseAlongSatMorToBoundaryPort B₁ PL {B₂ = Bp} satMorL sys

    rebaseHubToRight
      : ∀ {ℓName ℓWProver ℓWModel}
        {Name : Set ℓName}
      → SystemIO
          {ℓForm = ℓFormP}
          {ℓWProver = ℓWProver}
          {ℓWModel = ℓWModel}
          Name (LogOSSignature.∂Cosp SigP)
          (BulkBoundary.Con_bnd (LogicKernel.BB K))
          (BoundaryIO.Sat∂ Bp)
      → SystemIO↑
          {ℓForm = ℓFormR}
          {ℓWProver = ℓWProver}
          {ℓWModel = ℓWModel}
          Name (LogOSSignature.∂Cosp Sig₂)
          (BulkBoundary.Con_bnd (LogicKernel.BB K₂))
          (BoundaryIO.Sat∂ B₂)
    rebaseHubToRight sys =
      BoundarySystemIO.rebaseAlongSatMorToBoundaryPort B₂ PR {B₂ = Bp} satMorR sys

module ForKernel
  {ℓ : Level}
  {Sig₀ Sig₁ Sig₂ : LogOSSignature ℓ}
  (span : SigSpan Sig₀ Sig₁ Sig₂)
  (po   : SigPushout span)
  {Q : QAdapter ℓ}
  (K : Kernel (SigPushout.SigP po) Q)
  where

  open SigPushout po renaming (SigP to SigP; cocone to cocone)
  open SigCocone cocone renaming (inl to inl; inr to inr)

  K₁ : Kernel Sig₁ Q
  K₁ = reindexKernel inl K

  K₂ : Kernel Sig₂ Q
  K₂ = reindexKernel inr K

  Bp : BoundaryIO SigP Q (Kernel.HWorld K) (Kernel.BB K) (Kernel.HTruth K)
  Bp = KBoundary.boundaryIO K

  B₁ : BoundaryIO Sig₁ Q (Kernel.HWorld K₁) (Kernel.BB K₁) (Kernel.HTruth K₁)
  B₁ = KBoundary.boundaryIO K₁

  B₂ : BoundaryIO Sig₂ Q (Kernel.HWorld K₂) (Kernel.BB K₂) (Kernel.HTruth K₂)
  B₂ = KBoundary.boundaryIO K₂

  satHomL
    : SatHom (LogOSSignature.∂Cosp Sig₁) (BulkBoundary.Con_bnd (Kernel.BB K₁))
             (BoundaryIO.Sat∂ B₁)
             (LogOSSignature.∂Cosp SigP) (BulkBoundary.Con_bnd (Kernel.BB K))
             (BoundaryIO.Sat∂ Bp)
  satHomL = satHom-fromSatMor (satMor-reindexKernel-boundary inl K)

  satHomR
    : SatHom (LogOSSignature.∂Cosp Sig₂) (BulkBoundary.Con_bnd (Kernel.BB K₂))
             (BoundaryIO.Sat∂ B₂)
             (LogOSSignature.∂Cosp SigP) (BulkBoundary.Con_bnd (Kernel.BB K))
             (BoundaryIO.Sat∂ Bp)
  satHomR = satHom-fromSatMor (satMor-reindexKernel-boundary inr K)

  module Ports
    {ℓFormL ℓFormR ℓFormP : Level}
    (PL : BoundaryPort {ℓForm = ℓFormL} Sig₁ Q _ _ _ B₁)
    (PR : BoundaryPort {ℓForm = ℓFormR} Sig₂ Q _ _ _ B₂)
    (PP : BoundaryPort {ℓForm = ℓFormP} SigP Q _ _ _ Bp)
    where

    P₁ = toPresentationC B₁ PL
    P₂ = toPresentationC B₂ PR
    Ph = toPresentationC Bp PP

    LeftToHub : Interop.HeteroPortRefinement satHomL P₁ Ph
    LeftToHub = Interop.heteroCanonicalRefinement satHomL P₁ Ph

    RightToHub : Interop.HeteroPortRefinement satHomR P₂ Ph
    RightToHub = Interop.heteroCanonicalRefinement satHomR P₂ Ph

    mapL : BoundaryPort.Form PL → BoundaryPort.Form PP
    mapL = Interop.HeteroPortRefinement.map LeftToHub

    mapR : BoundaryPort.Form PR → BoundaryPort.Form PP
    mapR = Interop.HeteroPortRefinement.map RightToHub

    ObsLeViaHub
      : BoundaryPort.Form PL → BoundaryPort.Form PR → Set _
    ObsLeViaHub φ ψ = Prop.ObsLeOn (PresentationC.SatF Ph) (mapL φ) (mapR ψ)

    -- Pushout satisfaction condition (sound): each branch translates to the hub.
    left-sat→hub
      : ∀ p φ
      → BoundaryPort.SatF PL p φ
      → PresentationC.SatF Ph (SatHom.mapCtx satHomL p) (mapL φ)
    left-sat→hub p φ sat =
      Interop.HeteroPortRefinement.preserves-Sat LeftToHub p φ sat

    right-sat→hub
      : ∀ p φ
      → BoundaryPort.SatF PR p φ
      → PresentationC.SatF Ph (SatHom.mapCtx satHomR p) (mapR φ)
    right-sat→hub p φ sat =
      Interop.HeteroPortRefinement.preserves-Sat RightToHub p φ sat

    -- Any boundary refinement on a branch transports to the hub.
    liftLeftRefinement
      : Interop.PortRefinement B₁ PL PL
      → Interop.HeteroPortRefinement satHomL P₁ Ph
    liftLeftRefinement R =
      let
        R₁ = Interop.boundaryRefinementToHetero B₁ R
      in
      Interop.heteroComposeRefinement
        (idSatHom (BoundaryIO.Sat∂ B₁)) satHomL P₁ P₁ Ph R₁ LeftToHub

    liftRightRefinement
      : Interop.PortRefinement B₂ PR PR
      → Interop.HeteroPortRefinement satHomR P₂ Ph
    liftRightRefinement R =
      let
        R₂ = Interop.boundaryRefinementToHetero B₂ R
      in
      Interop.heteroComposeRefinement
        (idSatHom (BoundaryIO.Sat∂ B₂)) satHomR P₂ P₂ Ph R₂ RightToHub

module ForLogicKernel
  {ℓ : Level}
  {Sig₀ Sig₁ Sig₂ : LogOSSignature ℓ}
  (span : SigSpan Sig₀ Sig₁ Sig₂)
  (po   : SigPushout span)
  {Q : QAdapter ℓ}
  (K : LogicKernel (SigPushout.SigP po) Q)
  where

  open SigPushout po renaming (SigP to SigP; cocone to cocone)
  open SigCocone cocone renaming (inl to inl; inr to inr)

  K₁ : LogicKernel Sig₁ Q
  K₁ = reindexLogicKernel inl K

  K₂ : LogicKernel Sig₂ Q
  K₂ = reindexLogicKernel inr K

  Bp : BoundaryIO SigP Q (LogicKernel.HWorld K) (LogicKernel.BB K) (LogicKernel.HTruth K)
  Bp = LKBoundary.boundaryIO K

  B₁ : BoundaryIO Sig₁ Q (LogicKernel.HWorld K₁) (LogicKernel.BB K₁) (LogicKernel.HTruth K₁)
  B₁ = LKBoundary.boundaryIO K₁

  B₂ : BoundaryIO Sig₂ Q (LogicKernel.HWorld K₂) (LogicKernel.BB K₂) (LogicKernel.HTruth K₂)
  B₂ = LKBoundary.boundaryIO K₂

  satHomL
    : SatHom (LogOSSignature.∂Cosp Sig₁) (BulkBoundary.Con_bnd (LogicKernel.BB K₁))
             (BoundaryIO.Sat∂ B₁)
             (LogOSSignature.∂Cosp SigP) (BulkBoundary.Con_bnd (LogicKernel.BB K))
             (BoundaryIO.Sat∂ Bp)
  satHomL = satHom-fromSatMor (satMor-reindexLogicKernel-boundary inl K)

  satHomR
    : SatHom (LogOSSignature.∂Cosp Sig₂) (BulkBoundary.Con_bnd (LogicKernel.BB K₂))
             (BoundaryIO.Sat∂ B₂)
             (LogOSSignature.∂Cosp SigP) (BulkBoundary.Con_bnd (LogicKernel.BB K))
             (BoundaryIO.Sat∂ Bp)
  satHomR = satHom-fromSatMor (satMor-reindexLogicKernel-boundary inr K)

  module Ports
    {ℓFormL ℓFormR ℓFormP : Level}
    (PL : BoundaryPort {ℓForm = ℓFormL} Sig₁ Q _ _ _ B₁)
    (PR : BoundaryPort {ℓForm = ℓFormR} Sig₂ Q _ _ _ B₂)
    (PP : BoundaryPort {ℓForm = ℓFormP} SigP Q _ _ _ Bp)
    where

    P₁ = toPresentationC B₁ PL
    P₂ = toPresentationC B₂ PR
    Ph = toPresentationC Bp PP

    LeftToHub : Interop.HeteroPortRefinement satHomL P₁ Ph
    LeftToHub = Interop.heteroCanonicalRefinement satHomL P₁ Ph

    RightToHub : Interop.HeteroPortRefinement satHomR P₂ Ph
    RightToHub = Interop.heteroCanonicalRefinement satHomR P₂ Ph

    mapL : BoundaryPort.Form PL → BoundaryPort.Form PP
    mapL = Interop.HeteroPortRefinement.map LeftToHub

    mapR : BoundaryPort.Form PR → BoundaryPort.Form PP
    mapR = Interop.HeteroPortRefinement.map RightToHub

    ObsLeViaHub
      : BoundaryPort.Form PL → BoundaryPort.Form PR → Set _
    ObsLeViaHub φ ψ = Prop.ObsLeOn (PresentationC.SatF Ph) (mapL φ) (mapR ψ)

    -- Pushout satisfaction condition (sound): each branch translates to the hub.
    left-sat→hub
      : ∀ p φ
      → BoundaryPort.SatF PL p φ
      → PresentationC.SatF Ph (SatHom.mapCtx satHomL p) (mapL φ)
    left-sat→hub p φ sat =
      Interop.HeteroPortRefinement.preserves-Sat LeftToHub p φ sat

    right-sat→hub
      : ∀ p φ
      → BoundaryPort.SatF PR p φ
      → PresentationC.SatF Ph (SatHom.mapCtx satHomR p) (mapR φ)
    right-sat→hub p φ sat =
      Interop.HeteroPortRefinement.preserves-Sat RightToHub p φ sat

    -- Any boundary refinement on a branch transports to the hub.
    liftLeftRefinement
      : Interop.PortRefinement B₁ PL PL
      → Interop.HeteroPortRefinement satHomL P₁ Ph
    liftLeftRefinement R =
      let
        R₁ = Interop.boundaryRefinementToHetero B₁ R
      in
      Interop.heteroComposeRefinement
        (idSatHom (BoundaryIO.Sat∂ B₁)) satHomL P₁ P₁ Ph R₁ LeftToHub

    liftRightRefinement
      : Interop.PortRefinement B₂ PR PR
      → Interop.HeteroPortRefinement satHomR P₂ Ph
    liftRightRefinement R =
      let
        R₂ = Interop.boundaryRefinementToHetero B₂ R
      in
      Interop.heteroComposeRefinement
        (idSatHom (BoundaryIO.Sat∂ B₂)) satHomR P₂ P₂ Ph R₂ RightToHub
