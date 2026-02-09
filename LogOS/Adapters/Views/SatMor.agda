{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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

open import LogOS.Minimal.ConAlg
open import LogOS.Ports.Semantic.SatMor

open import LogOS.Kernel
open import LogOS.Kernel.Reindex
open import LogOS.Kernel.Hom
open import LogOS.Kernel.HomOverSig
import LogOS.Kernel.Tiers as LKT

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
    in SatMor
        (record
          { Ctx = LogOSSignature.∂Cosp Sig₁
          ; Con = Con_bnd
          ; Sat = Kernel.Sat_H_bnd (reindexKernel σ K)
          })
        (record
          { Ctx = LogOSSignature.∂Cosp Sig₂
          ; Con = Con_bnd
          ; Sat = Kernel.Sat_H_bnd K
          })
satMor-reindexKernel-boundary σ K =
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
  → SatMor
      (record
        { Ctx = LogOSSignature.Cosp Sig₁
        ; Con = Fml₁
        ; Sat = Truth.StrictTruth.StrictLayer.Sat_S (Kernel.Strict (reindexKernelWithFml σ K mapFml))
        })
      (record
        { Ctx = LogOSSignature.Cosp Sig₂
        ; Con = Kernel.Fml K
        ; Sat = Truth.StrictTruth.StrictLayer.Sat_S (Kernel.Strict K)
        })
satMor-reindexKernel-strict σ K mapFml =
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
    in SatMor
        (record
          { Ctx = LogOSSignature.Cosp Sig
          ; Con = Kernel.Fml K
          ; Sat = StrictLayer.Sat_S (Kernel.Strict K)
          })
        (record
          { Ctx = LogOSSignature.∂Cosp Sig
          ; Con = Con_bnd
          ; Sat = Kernel.Sat_H_bnd K
          })
satMor-strict-to-boundary {Sig = Sig} K =
  record
    { mapCtx = LogOSSignature.to∂ Sig
    ; mapCon = Kernel.TransH K
    ; sat-↔  = λ w φ →
        Prop.↔-trans
          (Kernel.coh-LH K w φ)
          (Kernel.sat-coh K w (Kernel.TransH K φ))
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
    SatMor
      (record
        { Ctx = LogOSSignature.Cosp Sig
        ; Con = Kernel.Code K
        ; Sat = λ w γ → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) (Kernel.decode K γ)
        })
      (record
        { Ctx = LogOSSignature.∂Cosp Sig
        ; Con = Con_bnd
        ; Sat = Kernel.Sat_H_bnd K
        })
satMor-code-to-boundary {Sig = Sig} K =
  record
    { mapCtx = LogOSSignature.to∂ Sig
    ; mapCon = Kernel.decode K
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
  → SatMor
      (record
        { Ctx = LogOSSignature.∂Cosp Sig
        ; Con = BulkBoundary.Con_bnd (Kernel.BB K₁)
        ; Sat = Kernel.Sat_H_bnd K₁
        })
      (record
        { Ctx = LogOSSignature.∂Cosp Sig
        ; Con = BulkBoundary.Con_bnd (Kernel.BB K₂)
        ; Sat = Kernel.Sat_H_bnd K₂
        })
satMor-of-KernelHom-boundary {Sig = Sig} h hs =
  record
    { mapCtx = λ p → p
    ; mapCon = ConAlgHom≡.map∂ (KernelHom.con-hom h)
    ; sat-↔  = KernelHomBoundarySat.sat-↔ hs
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
    SatMor
      (record
        { Ctx = LogOSSignature.∂Cosp Sig₁
        ; Con = BulkBoundary.Con_bnd (Kernel.BB K₁)
        ; Sat = Kernel.Sat_H_bnd K₁
        })
      (record
        { Ctx = LogOSSignature.∂Cosp Sig₂
        ; Con = BulkBoundary.Con_bnd (Kernel.BB K₂)
        ; Sat = Kernel.Sat_H_bnd K₂
        })
satMor-of-KernelHomOver-boundary {K₂ = K₂} h hs =
  let
    σ = KernelHomOver.σ h
    hom = KernelHomOver.hom h

    m₁ = satMor-of-KernelHom-boundary hom hs
    m₂ = satMor-reindexKernel-boundary σ K₂
  in
  composeSatMor m₁ m₂
