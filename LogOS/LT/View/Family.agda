{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.View.Family where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Indexed families of Views into a shared boundary.
--
-- This module isolates a recurring pattern in LogOS:
-- many code domains, one observational boundary.
--
-- The key construction is `bundleView`, which turns an indexed family of Views
-- `(i : Ix) → View (Code i) B` into a single View on the Σ-bundle of codes.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.View using (View; μ)
open import LogOS.LT.Kernel using (Kernel; kernelFromView)

record IndexedViewFamily
  {ℓB ℓRel ℓI ℓCode : Level}
  (B : ConPreorder ℓB ℓRel)
  : Set (lsuc (ℓB ⊔ ℓRel ⊔ ℓI ⊔ ℓCode)) where
  field
    Ix   : Set ℓI
    Code : Ix → Set ℓCode
    view : (i : Ix) → View (Code i) B

open IndexedViewFamily public

record FamilyCodeR
  {ℓB ℓRel ℓI ℓCode : Level} {B : ConPreorder ℓB ℓRel}
  (F : IndexedViewFamily {ℓI = ℓI} {ℓCode = ℓCode} B)
  : Set (ℓI ⊔ ℓCode) where
  constructor mkFamilyCodeR
  field
    ix   : Ix F
    code : Code F ix

open FamilyCodeR public

FamilyCode
  : ∀ {ℓB ℓRel ℓI ℓCode : Level} {B : ConPreorder ℓB ℓRel}
  → IndexedViewFamily {ℓI = ℓI} {ℓCode = ℓCode} B
  → Set (ℓI ⊔ ℓCode)
FamilyCode F = FamilyCodeR F

bundleView
  : ∀ {ℓB ℓRel ℓI ℓCode : Level} {B : ConPreorder ℓB ℓRel}
  → (F : IndexedViewFamily {ℓI = ℓI} {ℓCode = ℓCode} B)
  → View (FamilyCode F) B
bundleView F =
  record
    { μ = λ fc → μ (view F (ix fc)) (code fc) }

bundleKernel
  : ∀ {ℓB ℓRel ℓI ℓCode : Level} {B : ConPreorder ℓB ℓRel}
  → IndexedViewFamily {ℓI = ℓI} {ℓCode = ℓCode} B
  → Kernel ℓB ℓRel (ℓI ⊔ ℓCode)
bundleKernel F = kernelFromView (bundleView F)
