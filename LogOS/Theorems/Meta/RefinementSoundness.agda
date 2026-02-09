{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel
open import LogOS.Kernel as LK

import LogOS.Kernel.Hom2Cat as K2
import LogOS.Kernel.Hom as KHom
import LogOS.Kernel.Hom2Cat as LK2

-- ============================================================================
-- Kernel level (uniform S/H/code + parameterised G-tier)
-- ============================================================================

module KernelSoundness
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  where

  private
    Cosp = LogOSSignature.Cosp Sig
    ∂Cosp = LogOSSignature.∂Cosp Sig

  module _ {K₁ K₂ : LK.Kernel Sig Q} {f g : LK2.KernelHom₁ K₁ K₂} where
    module HT₂ = Truth.HomotypicalTruth Sig Q (LK.Kernel.HWorld K₂)
    module ST₂ = Truth.StrictTruth Sig

    refine-preserves-Sat_H
      : LK2._⇒_ f g
      → ∀ (w : Cosp) (γ : LK.Kernel.Code K₁)
      → HT₂.HLayer.Sat_H (LK.Kernel.HTruth K₂) w
          (LK.Kernel.decode K₂ (LK2.KernelHom₁.mapCode₁ f γ))
      → HT₂.HLayer.Sat_H (LK.Kernel.HTruth K₂) w
          (LK.Kernel.decode K₂ (LK2.KernelHom₁.mapCode₁ g γ))
    refine-preserves-Sat_H fg w γ sat =
      HT₂.HLayer.mono-Con (LK.Kernel.HTruth K₂) (fg γ) sat

    refine-preserves-Sat_H_bnd
      : LK2._⇒_ f g
      → ∀ (w : Cosp) (γ : LK.Kernel.Code K₁)
      → LK.Kernel.Sat_H_bnd K₂ (LogOSSignature.to∂ Sig w)
          (LK.Kernel.decode K₂ (LK2.KernelHom₁.mapCode₁ f γ))
      → LK.Kernel.Sat_H_bnd K₂ (LogOSSignature.to∂ Sig w)
          (LK.Kernel.decode K₂ (LK2.KernelHom₁.mapCode₁ g γ))
    refine-preserves-Sat_H_bnd fg w γ sat∂ =
      let
        cohF = LK.Kernel.sat-coh K₂ w _
        cohG = LK.Kernel.sat-coh K₂ w _
        satH : HT₂.HLayer.Sat_H (LK.Kernel.HTruth K₂) w
                 (LK.Kernel.decode K₂ (LK2.KernelHom₁.mapCode₁ f γ))
        satH = Prop._↔_.from cohF sat∂
        satH' = refine-preserves-Sat_H fg w γ satH
      in Prop._↔_.to cohG satH'

    refine-preserves-Sat_H_bnd˘
      : LK2._⇒_ g f
      → ∀ (w : Cosp) (γ : LK.Kernel.Code K₁)
      → LK.Kernel.Sat_H_bnd K₂ (LogOSSignature.to∂ Sig w)
          (LK.Kernel.decode K₂ (LK2.KernelHom₁.mapCode₁ g γ))
      → LK.Kernel.Sat_H_bnd K₂ (LogOSSignature.to∂ Sig w)
          (LK.Kernel.decode K₂ (LK2.KernelHom₁.mapCode₁ f γ))
    refine-preserves-Sat_H_bnd˘ gf w γ sat∂ =
      let
        cohG = LK.Kernel.sat-coh K₂ w _
        cohF = LK.Kernel.sat-coh K₂ w _
        satH : HT₂.HLayer.Sat_H (LK.Kernel.HTruth K₂) w
                 (LK.Kernel.decode K₂ (LK2.KernelHom₁.mapCode₁ g γ))
        satH = Prop._↔_.from cohG sat∂
        satH' : HT₂.HLayer.Sat_H (LK.Kernel.HTruth K₂) w
                  (LK.Kernel.decode K₂ (LK2.KernelHom₁.mapCode₁ f γ))
        satH' = HT₂.HLayer.mono-Con (LK.Kernel.HTruth K₂) (gf γ) satH
      in Prop._↔_.to cohF satH'

    approx-preserves-Sat_H_bnd
      : LK2._≈_ f g
      → ∀ (w : Cosp) (γ : LK.Kernel.Code K₁)
      → LK.Kernel.Sat_H_bnd K₂ (LogOSSignature.to∂ Sig w)
          (LK.Kernel.decode K₂ (LK2.KernelHom₁.mapCode₁ f γ))
        ↔ LK.Kernel.Sat_H_bnd K₂ (LogOSSignature.to∂ Sig w)
            (LK.Kernel.decode K₂ (LK2.KernelHom₁.mapCode₁ g γ))
    approx-preserves-Sat_H_bnd (fg , gf) w γ =
      record
        { to   = refine-preserves-Sat_H_bnd fg w γ
        ; from = refine-preserves-Sat_H_bnd˘ gf w γ
        }
