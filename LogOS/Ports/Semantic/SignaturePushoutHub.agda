{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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
open import LogOS.Ports.Semantic.SatMor using (SatMor; SatHom; satHom-fromSatMor; idSatHomS)
open import LogOS.Ports.Semantic.Core using (boundarySatSystemFromIO)
open import LogOS.Ports.Semantic.SatSystemIO using (SatSystemIO; SatSystemIO↑)
import LogOS.Ports.Semantic.BoundarySystemIO as BoundarySystemIO
import LogOS.Ports.Semantic.Interoperability as Interop
open import LogOS.Syntax.Prop as Prop

open import LogOS.System using (fromBoundaryIO)

open import LogOS.Kernel
import LogOS.Boundary.FromKernel as KBoundary
open import LogOS.Kernel.Reindex using (reindexKernel)

open import LogOS.Adapters.Views.SatMor using
  ( satMor-reindexKernel-boundary
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

  -- Boundary-facing systems (Ctx = ∂Cosp, Con = Con_bnd, Sat = Sat∂).
  S₁ = boundarySatSystemFromIO B₁
  S₂ = boundarySatSystemFromIO B₂
  Sp = boundarySatSystemFromIO Bp

  satMorL
    : SatMor
        S₁
        Sp
  satMorL = satMor-reindexKernel-boundary inl K

  satMorR
    : SatMor
        S₂
        Sp
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

    Obs≈ViaHub
      : BoundaryPort.Form PL → BoundaryPort.Form PR → Set _
    Obs≈ViaHub φ ψ = PresentationC.Obs≈F Ph (mapL φ) (mapR ψ)

    infix 4 _≈ViaHub_
    _≈ViaHub_
      : BoundaryPort.Form PL → BoundaryPort.Form PR → Set _
    φ ≈ViaHub ψ = PresentationC.Obs≈F Ph (mapL φ) (mapR ψ)

    ObsEqViaHub↔≈ViaHub
      : ∀ {φ ψ} → Prop._↔_ (ObsEqViaHub φ ψ) (φ ≈ViaHub ψ)
    ObsEqViaHub↔≈ViaHub {φ} {ψ} =
      PresentationC.ObsEqF↔Obs≈F Ph {x = mapL φ} {y = mapR ψ}

    ObsEqViaHub↔Obs≈ViaHub
      : ∀ {φ ψ} → Prop._↔_ (ObsEqViaHub φ ψ) (Obs≈ViaHub φ ψ)
    ObsEqViaHub↔Obs≈ViaHub = ObsEqViaHub↔≈ViaHub

    rebaseHubToLeft
      : ∀ {ℓName ℓWProver ℓWModel}
        {Name : Set ℓName}
      → SatSystemIO
          {ℓForm = ℓFormP}
          {ℓWProver = ℓWProver}
          {ℓWModel = ℓWModel}
          Name Sp
      → SatSystemIO↑
          {ℓForm = ℓFormL}
          {ℓWProver = ℓWProver}
          {ℓWModel = ℓWModel}
          Name S₁
    rebaseHubToLeft sys =
      let module Bio = BoundarySystemIO.ForSystem (fromBoundaryIO B₁) in
      Bio.rebaseAlongSatMorToBoundaryPortS PL {B₂ = Bp} satMorL sys

    rebaseHubToRight
      : ∀ {ℓName ℓWProver ℓWModel}
        {Name : Set ℓName}
      → SatSystemIO
          {ℓForm = ℓFormP}
          {ℓWProver = ℓWProver}
          {ℓWModel = ℓWModel}
          Name Sp
      → SatSystemIO↑
          {ℓForm = ℓFormR}
          {ℓWProver = ℓWProver}
          {ℓWModel = ℓWModel}
          Name S₂
    rebaseHubToRight sys =
      let module Bio = BoundarySystemIO.ForSystem (fromBoundaryIO B₂) in
      Bio.rebaseAlongSatMorToBoundaryPortS PR {B₂ = Bp} satMorR sys

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

  -- Boundary-facing systems (Ctx = ∂Cosp, Con = Con_bnd, Sat = Sat∂).
  S₁ = boundarySatSystemFromIO B₁
  S₂ = boundarySatSystemFromIO B₂
  Sp = boundarySatSystemFromIO Bp

  satHomL
    : SatHom
        S₁
        Sp
  satHomL = satHom-fromSatMor (satMor-reindexKernel-boundary inl K)

  satHomR
    : SatHom
        S₂
        Sp
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
        idSatHomS satHomL P₁ P₁ Ph R₁ LeftToHub

    liftRightRefinement
      : Interop.PortRefinement B₂ PR PR
      → Interop.HeteroPortRefinement satHomR P₂ Ph
    liftRightRefinement R =
      let
        R₂ = Interop.boundaryRefinementToHetero B₂ R
      in
      Interop.heteroComposeRefinement
        idSatHomS satHomR P₂ P₂ Ph R₂ RightToHub
