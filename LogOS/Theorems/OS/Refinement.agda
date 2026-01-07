{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.OS.Refinement where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Kernel.Endo

-- OS-style refinement/simulation:
-- refinement of endomaps (`f ≤₂ g`) implies preservation of all “safety”
-- observations (monotone w.r.t. the boundary preorder) at the H-tier.
--
-- This is *derivable from kernel axioms* because Sat_H is monotone in constraints.

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (K : Kernel Sig Q) where
  open LogOSSignature Sig using (Cosp)
  open Kernel K
  private
    CP = BulkBoundary.bnd BB
    module CP = ConPoset CP
    module HT = Truth.HomotypicalTruth Sig Q HWorld

  refine-preserves-Sat_H
    : ∀ {f g : Endo K}
    → _≤₂_ K f g
    → ∀ {w c} → HT.HLayer.Sat_H HTruth w (Endo.fn f c)
              → HT.HLayer.Sat_H HTruth w (Endo.fn g c)
  refine-preserves-Sat_H {f} {g} f≤g {w} {c} sat =
    HT.HLayer.mono-Con HTruth (f≤g c) sat

  refine-preserves-ObsEq→ObsImp
    : ∀ {f g : Endo K}
    → _≤₂_ K f g
    → ∀ c (w : Cosp)
    → (HT.HLayer.Sat_H HTruth w (Endo.fn f c))
      → (HT.HLayer.Sat_H HTruth w (Endo.fn g c))
  refine-preserves-ObsEq→ObsImp {f} {g} f≤g c w sat =
    refine-preserves-Sat_H {f = f} {g = g} f≤g {w = w} {c = c} sat
