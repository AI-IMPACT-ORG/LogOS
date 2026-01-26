{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.Views.SatMor where

-- Canonical satisfaction morphisms induced by LogOS “view” adapters:
-- - signature reindexing (pullback) along `SigHom`
-- - kernel/logic-kernel morphisms, under explicit satisfaction assumptions
--
-- These are the key ingredients needed to apply the heterogeneous interlingua
-- theorems across changing logic systems.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Base.Signature
open import LogOS.Base.Signature.Hom
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth

open import LogOS.Algebra.ConAlg
open import LogOS.Ports.Semantic.SatMor

open import LogOS.Kernel
open import LogOS.Kernel.Reindex
open import LogOS.Kernel.Hom
open import LogOS.Kernel.HomOverSig

open import LogOS.Kernel.LogicKernel
open import LogOS.Kernel.LogicKernel.Reindex
open import LogOS.Kernel.LogicKernel.Hom
open import LogOS.Kernel.LogicKernel.HomOverSig
import LogOS.Kernel.LogicKernel.Tiers as LKT

-- ---------------------------------------------------------------------------
-- Signature reindexing induces a satisfaction morphism (boundary satisfaction).
-- ---------------------------------------------------------------------------

satMor-reindexKernel-boundary
  : ∀ {ℓ : Level}
    {Sig₁ Sig₂ : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
  → let BB = Kernel.BB K
        open BulkBoundary BB
    in SatMor (LogOSSignature.∂Cosp Sig₁) Con_bnd (Kernel.Sat_H_bnd (reindexKernel σ K))
              (LogOSSignature.∂Cosp Sig₂) Con_bnd (Kernel.Sat_H_bnd K)
satMor-reindexKernel-boundary σ K =
  record
    { mapCtx = SigHom.map∂Cosp σ
    ; mapCon = λ c → c
    ; sat-↔  = λ p c → reindex-sat-bnd σ K p c
    }

satMor-reindexLogicKernel-boundary
  : ∀ {ℓ : Level}
    {Sig₁ Sig₂ : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : LogicKernel Sig₂ Q)
  → let BB = LogicKernel.BB K
        open BulkBoundary BB
    in SatMor (LogOSSignature.∂Cosp Sig₁) Con_bnd (LogicKernel.Sat_H_bnd (reindexLogicKernel σ K))
              (LogOSSignature.∂Cosp Sig₂) Con_bnd (LogicKernel.Sat_H_bnd K)
satMor-reindexLogicKernel-boundary σ K =
  record
    { mapCtx = SigHom.map∂Cosp σ
    ; mapCon = λ c → c
    ; sat-↔  = λ p c → reindexLogic-sat-bnd σ K p c
    }

-- ---------------------------------------------------------------------------
-- Signature reindexing induces a satisfaction morphism (strict satisfaction).
-- ---------------------------------------------------------------------------

satMor-reindexKernel-strict
  : ∀ {ℓ : Level}
    {Sig₁ Sig₂ : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : Kernel Sig₂ Q)
    {Fml₁ : Set ℓ}
  → (mapFml : Fml₁ → Kernel.Fml K)
  → SatMor (LogOSSignature.Cosp Sig₁) Fml₁
           (Truth.StrictTruth.StrictLayer.Sat_S (Kernel.Strict (reindexKernelWithFml σ K mapFml)))
           (LogOSSignature.Cosp Sig₂) (Kernel.Fml K)
           (Truth.StrictTruth.StrictLayer.Sat_S (Kernel.Strict K))
satMor-reindexKernel-strict σ K mapFml =
  record
    { mapCtx = SigHom.mapCosp σ
    ; mapCon = mapFml
    ; sat-↔  = λ p φ → reindex-satS-withFml σ K mapFml p φ
    }

satMor-reindexLogicKernel-strict
  : ∀ {ℓ : Level}
    {Sig₁ Sig₂ : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (σ : SigHom Sig₁ Sig₂)
    (K : LogicKernel Sig₂ Q)
    {Fml₁ : Set ℓ}
  → (mapFml : Fml₁ → LogicKernel.Fml K)
  → SatMor (LogOSSignature.Cosp Sig₁) Fml₁
           (Truth.StrictTruth.StrictLayer.Sat_S (LogicKernel.Strict (reindexLogicKernelWithFml σ K mapFml)))
           (LogOSSignature.Cosp Sig₂) (LogicKernel.Fml K)
           (Truth.StrictTruth.StrictLayer.Sat_S (LogicKernel.Strict K))
satMor-reindexLogicKernel-strict σ K mapFml =
  record
    { mapCtx = SigHom.mapCosp σ
    ; mapCon = mapFml
    ; sat-↔  = λ p φ → reindexLogic-satS-withFml σ K mapFml p φ
    }

-- ---------------------------------------------------------------------------
-- Strict satisfaction to boundary satisfaction (kernel coherence as SatMor).
-- ---------------------------------------------------------------------------

satMor-strict-to-boundary
  : ∀ {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → let open BulkBoundary (Kernel.BB K)
        open Truth.StrictTruth Sig
        module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K)
    in SatMor (LogOSSignature.Cosp Sig) (Kernel.Fml K)
              (StrictLayer.Sat_S (Kernel.Strict K))
              (LogOSSignature.∂Cosp Sig) Con_bnd (Kernel.Sat_H_bnd K)
satMor-strict-to-boundary {Sig = Sig} K =
  record
    { mapCtx = LogOSSignature.to∂ Sig
    ; mapCon = Kernel.TransH K
    ; sat-↔  = λ w φ →
        Prop.↔-trans
          (Kernel.coh-LH K w φ)
          (Kernel.sat-coh K w (Kernel.TransH K φ))
    }

satMor-strict-to-boundaryLogic
  : ∀ {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → let open BulkBoundary (LogicKernel.BB K)
        open Truth.StrictTruth Sig
        module HT = Truth.HomotypicalTruth Sig Q (LogicKernel.HWorld K)
    in SatMor (LogOSSignature.Cosp Sig) (LogicKernel.Fml K)
              (StrictLayer.Sat_S (LogicKernel.Strict K))
              (LogOSSignature.∂Cosp Sig) Con_bnd (LogicKernel.Sat_H_bnd K)
satMor-strict-to-boundaryLogic {Sig = Sig} K =
  record
    { mapCtx = LogOSSignature.to∂ Sig
    ; mapCon = LogicKernel.TransH K
    ; sat-↔  = λ w φ →
        Prop.↔-trans
          (LogicKernel.coh-LH K w φ)
          (LogicKernel.sat-coh K w (LogicKernel.TransH K φ))
    }

-- ---------------------------------------------------------------------------
-- Reflection (code) to boundary satisfaction as a SatMor.
-- ---------------------------------------------------------------------------

satMor-code-to-boundary
  : ∀ {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → let open BulkBoundary (Kernel.BB K) in
    SatMor (LogOSSignature.Cosp Sig) (Kernel.Code K)
           (λ w γ → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) (Kernel.decode K γ))
           (LogOSSignature.∂Cosp Sig) Con_bnd (Kernel.Sat_H_bnd K)
satMor-code-to-boundary {Sig = Sig} K =
  record
    { mapCtx = LogOSSignature.to∂ Sig
    ; mapCon = Kernel.decode K
    ; sat-↔  = λ _ _ → Prop.↔-refl
    }

satMor-code-to-boundaryLogic
  : ∀ {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    (K : LogicKernel Sig Q)
  → let open BulkBoundary (LogicKernel.BB K)
        module R = LKT.For K
    in SatMor (LogOSSignature.Cosp Sig) (LogicKernel.Code K) (R.Sat_R)
              (LogOSSignature.∂Cosp Sig) Con_bnd (LogicKernel.Sat_H_bnd K)
satMor-code-to-boundaryLogic {Sig = Sig} K =
  record
    { mapCtx = LogOSSignature.to∂ Sig
    ; mapCon = LogicKernel.decode K
    ; sat-↔  = λ _ _ → Prop.↔-refl
    }

-- ---------------------------------------------------------------------------
-- Kernel homs do not *a priori* talk about satisfaction; keep it explicit.
-- ---------------------------------------------------------------------------

record KernelHomBoundarySat
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K₁ K₂ : Kernel Sig Q)
  (h : KernelHom K₁ K₂)
  : Set (lsuc (lsuc ℓ)) where
  open Kernel K₁ renaming (BB to BB₁)
  open Kernel K₂ renaming (BB to BB₂)
  open BulkBoundary BB₁ using (Con_bnd)
  open KernelHom h
  field
    sat-↔
      : ∀ p (c : Con_bnd)
      → Kernel.Sat_H_bnd K₁ p c ↔ Kernel.Sat_H_bnd K₂ p (ConAlgHom≡.map∂ con-hom c)

satMor-of-KernelHom-boundary
  : ∀ {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {K₁ K₂ : Kernel Sig Q}
    (h : KernelHom K₁ K₂)
    (hs : KernelHomBoundarySat K₁ K₂ h)
  → SatMor (LogOSSignature.∂Cosp Sig)
           (BulkBoundary.Con_bnd (Kernel.BB K₁)) (Kernel.Sat_H_bnd K₁)
           (LogOSSignature.∂Cosp Sig)
           (BulkBoundary.Con_bnd (Kernel.BB K₂)) (Kernel.Sat_H_bnd K₂)
satMor-of-KernelHom-boundary {Sig = Sig} h hs =
  record
    { mapCtx = λ p → p
    ; mapCon = ConAlgHom≡.map∂ (KernelHom.con-hom h)
    ; sat-↔  = KernelHomBoundarySat.sat-↔ hs
    }

record LogicKernelHomBoundarySat
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K₁ K₂ : LogicKernel Sig Q)
  (h : LogicKernelHom K₁ K₂)
  : Set (lsuc (lsuc ℓ)) where
  open LogicKernel K₁ renaming (BB to BB₁)
  open LogicKernel K₂ renaming (BB to BB₂)
  open BulkBoundary BB₁ using (Con_bnd)
  open LogicKernelHom h
  field
    sat-↔
      : ∀ p (c : Con_bnd)
      → LogicKernel.Sat_H_bnd K₁ p c ↔ LogicKernel.Sat_H_bnd K₂ p (ConAlgHom≡.map∂ con-hom c)

satMor-of-LogicKernelHom-boundary
  : ∀ {ℓ : Level}
    {Sig : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {K₁ K₂ : LogicKernel Sig Q}
    (h : LogicKernelHom K₁ K₂)
    (hs : LogicKernelHomBoundarySat K₁ K₂ h)
  → SatMor (LogOSSignature.∂Cosp Sig)
           (BulkBoundary.Con_bnd (LogicKernel.BB K₁)) (LogicKernel.Sat_H_bnd K₁)
           (LogOSSignature.∂Cosp Sig)
           (BulkBoundary.Con_bnd (LogicKernel.BB K₂)) (LogicKernel.Sat_H_bnd K₂)
satMor-of-LogicKernelHom-boundary {Sig = Sig} h hs =
  record
    { mapCtx = λ p → p
    ; mapCon = ConAlgHom≡.map∂ (LogicKernelHom.con-hom h)
    ; sat-↔  = LogicKernelHomBoundarySat.sat-↔ hs
    }

-- ---------------------------------------------------------------------------
-- Heterogeneous kernel morphisms (over `SigHom`) induce satisfaction morphisms
-- by composing: (kernel-hom satisfaction) ∘ (reindex satisfaction).
-- ---------------------------------------------------------------------------

satMor-of-KernelHomOver-boundary
  : ∀ {ℓ : Level}
    {Sig₁ Sig₂ : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {K₁ : Kernel Sig₁ Q}
    {K₂ : Kernel Sig₂ Q}
    (h : KernelHomOver K₁ K₂)
    (hs : KernelHomBoundarySat K₁ (reindexKernel (KernelHomOver.σ h) K₂) (KernelHomOver.hom h))
  → let σ = KernelHomOver.σ h in
    SatMor (LogOSSignature.∂Cosp Sig₁)
           (BulkBoundary.Con_bnd (Kernel.BB K₁)) (Kernel.Sat_H_bnd K₁)
           (LogOSSignature.∂Cosp Sig₂)
           (BulkBoundary.Con_bnd (Kernel.BB K₂)) (Kernel.Sat_H_bnd K₂)
satMor-of-KernelHomOver-boundary {K₂ = K₂} h hs =
  let
    σ = KernelHomOver.σ h
    hom = KernelHomOver.hom h

    m₁ = satMor-of-KernelHom-boundary hom hs
    m₂ = satMor-reindexKernel-boundary σ K₂
  in
  composeSatMor m₁ m₂

satMor-of-LogicKernelHomOver-boundary
  : ∀ {ℓ : Level}
    {Sig₁ Sig₂ : LogOSSignature ℓ}
    {Q : QAdapter ℓ}
    {K₁ : LogicKernel Sig₁ Q}
    {K₂ : LogicKernel Sig₂ Q}
    (h : LogicKernelHomOver K₁ K₂)
    (hs : LogicKernelHomBoundarySat K₁ (reindexLogicKernel (LogicKernelHomOver.σ h) K₂) (LogicKernelHomOver.hom h))
  → let σ = LogicKernelHomOver.σ h in
    SatMor (LogOSSignature.∂Cosp Sig₁)
           (BulkBoundary.Con_bnd (LogicKernel.BB K₁)) (LogicKernel.Sat_H_bnd K₁)
           (LogOSSignature.∂Cosp Sig₂)
           (BulkBoundary.Con_bnd (LogicKernel.BB K₂)) (LogicKernel.Sat_H_bnd K₂)
satMor-of-LogicKernelHomOver-boundary {K₂ = K₂} h hs =
  let
    σ = LogicKernelHomOver.σ h
    hom = LogicKernelHomOver.hom h

    m₁ = satMor-of-LogicKernelHom-boundary hom hs
    m₂ = satMor-reindexLogicKernel-boundary σ K₂
  in
  composeSatMor m₁ m₂
