{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.RefinementSoundness where

-- Refinement soundness for the kernel 2-cell calculus:
-- a 2-cell `f ⇒ g` is not just “code map refines code map”, it also implies
-- semantic monotonicity for satisfaction predicates, by reusing the kernel’s
-- built-in monotonicity of `Sat_H` in boundary constraints.
--
-- This aligns the 2-category picture with the observer semantics reading:
-- “more refined morphisms preserve at least as much truth”.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_; intro)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPoset; BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel
open import LogOS.Kernel.LogicKernel as LK

import LogOS.Kernel.Hom2Cat as K2
import LogOS.Kernel.Hom as KHom
import LogOS.Kernel.LogicKernel.Hom2Cat as LK2

-- ============================================================================
-- LogicKernel level (uniform S/H/code + parameterised G-tier)
-- ============================================================================

module LogicKernelSoundness
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  where

  private
    Cosp = LogOSSignature.Cosp Sig
    ∂Cosp = LogOSSignature.∂Cosp Sig

  module _ {K₁ K₂ : LK.LogicKernel Sig Q} {f g : LK2.LogicKernelHom₁ K₁ K₂} where
    module HT₂ = Truth.HomotypicalTruth Sig Q (LK.LogicKernel.HWorld K₂)
    module ST₂ = Truth.StrictTruth Sig

    refine-preserves-Sat_H
      : LK2._⇒_ f g
      → ∀ (w : Cosp) (γ : LK.LogicKernel.Code K₁)
      → HT₂.HLayer.Sat_H (LK.LogicKernel.HTruth K₂) w
          (LK.LogicKernel.decode K₂ (LK2.LogicKernelHom₁.mapCode₁ f γ))
      → HT₂.HLayer.Sat_H (LK.LogicKernel.HTruth K₂) w
          (LK.LogicKernel.decode K₂ (LK2.LogicKernelHom₁.mapCode₁ g γ))
    refine-preserves-Sat_H fg w γ sat =
      HT₂.HLayer.mono-Con (LK.LogicKernel.HTruth K₂) (fg γ) sat

    refine-preserves-Sat_H_bnd
      : LK2._⇒_ f g
      → ∀ (w : Cosp) (γ : LK.LogicKernel.Code K₁)
      → LK.LogicKernel.Sat_H_bnd K₂ (LogOSSignature.to∂ Sig w)
          (LK.LogicKernel.decode K₂ (LK2.LogicKernelHom₁.mapCode₁ f γ))
      → LK.LogicKernel.Sat_H_bnd K₂ (LogOSSignature.to∂ Sig w)
          (LK.LogicKernel.decode K₂ (LK2.LogicKernelHom₁.mapCode₁ g γ))
    refine-preserves-Sat_H_bnd fg w γ sat∂ =
      let
        cohF = LK.LogicKernel.sat-coh K₂ w _
        cohG = LK.LogicKernel.sat-coh K₂ w _
        satH : HT₂.HLayer.Sat_H (LK.LogicKernel.HTruth K₂) w
                 (LK.LogicKernel.decode K₂ (LK2.LogicKernelHom₁.mapCode₁ f γ))
        satH = Prop._↔_.from cohF sat∂
        satH' = refine-preserves-Sat_H fg w γ satH
      in Prop._↔_.to cohG satH'

    refine-preserves-Sat_H_bnd˘
      : LK2._⇒_ g f
      → ∀ (w : Cosp) (γ : LK.LogicKernel.Code K₁)
      → LK.LogicKernel.Sat_H_bnd K₂ (LogOSSignature.to∂ Sig w)
          (LK.LogicKernel.decode K₂ (LK2.LogicKernelHom₁.mapCode₁ g γ))
      → LK.LogicKernel.Sat_H_bnd K₂ (LogOSSignature.to∂ Sig w)
          (LK.LogicKernel.decode K₂ (LK2.LogicKernelHom₁.mapCode₁ f γ))
    refine-preserves-Sat_H_bnd˘ gf w γ sat∂ =
      let
        cohG = LK.LogicKernel.sat-coh K₂ w _
        cohF = LK.LogicKernel.sat-coh K₂ w _
        satH : HT₂.HLayer.Sat_H (LK.LogicKernel.HTruth K₂) w
                 (LK.LogicKernel.decode K₂ (LK2.LogicKernelHom₁.mapCode₁ g γ))
        satH = Prop._↔_.from cohG sat∂
        satH' : HT₂.HLayer.Sat_H (LK.LogicKernel.HTruth K₂) w
                  (LK.LogicKernel.decode K₂ (LK2.LogicKernelHom₁.mapCode₁ f γ))
        satH' = HT₂.HLayer.mono-Con (LK.LogicKernel.HTruth K₂) (gf γ) satH
      in Prop._↔_.to cohF satH'

    approx-preserves-Sat_H_bnd
      : LK2._≈_ f g
      → ∀ (w : Cosp) (γ : LK.LogicKernel.Code K₁)
      → LK.LogicKernel.Sat_H_bnd K₂ (LogOSSignature.to∂ Sig w)
          (LK.LogicKernel.decode K₂ (LK2.LogicKernelHom₁.mapCode₁ f γ))
        ↔ LK.LogicKernel.Sat_H_bnd K₂ (LogOSSignature.to∂ Sig w)
            (LK.LogicKernel.decode K₂ (LK2.LogicKernelHom₁.mapCode₁ g γ))
    approx-preserves-Sat_H_bnd (fg , gf) w γ =
      record
        { to   = refine-preserves-Sat_H_bnd fg w γ
        ; from = refine-preserves-Sat_H_bnd˘ gf w γ
        }

-- ============================================================================
-- Kernel level (unguarded G-tier): inherited from LogicKernel via the wrapper
-- ============================================================================

module KernelSoundness
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  where

  private
    Cosp = LogOSSignature.Cosp Sig

  module _ {K₁ K₂ : Kernel Sig Q} {f g : K2.KernelHom₁ K₁ K₂} where
    module HT₂ = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K₂)

    refine-preserves-Sat_H
      : K2._⇒_ f g
      → ∀ (w : Cosp) (γ : Kernel.Code K₁)
      → HT₂.HLayer.Sat_H (Kernel.HTruth K₂) w
          (Kernel.decode K₂ (KHom.KernelHom.mapCode (K2.homKernel f) γ))
      → HT₂.HLayer.Sat_H (Kernel.HTruth K₂) w
          (Kernel.decode K₂ (KHom.KernelHom.mapCode (K2.homKernel g) γ))
    refine-preserves-Sat_H fg w γ sat =
      HT₂.HLayer.mono-Con (Kernel.HTruth K₂) (fg γ) sat
