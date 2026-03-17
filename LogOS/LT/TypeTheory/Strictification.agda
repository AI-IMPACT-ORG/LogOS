{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.TypeTheory.Strictification where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Equality-based type-theory aliases over the LT spine.

open import LogOS.Prelude
open import LogOS.LT.Kernel using (Kernel)
import LogOS.LT.Hom.Strictification as Hom
import LogOS.LT.TypeTheory.Surface as Surface
import LogOS.LT.TypeTheory.Core as Core

open Core public

Tm≡
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ : Level}
  → Kernel ℓ ℓRel ℓCode₁
  → Kernel ℓ ℓRel ℓCode₂
  → Set _
Tm≡ = Hom.KernelHom≡

decode-tm≡
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ : Level}
    {K : Kernel ℓ ℓRel ℓCode₁}
    {K' : Kernel ℓ ℓRel ℓCode₂}
  → (h : Tm≡ K K')
  → ∀ γ
  → LogOS.LT.Kernel.decode K' (Hom.mapCode h γ) ≡ Hom.map∂ h (LogOS.LT.Kernel.decode K γ)
decode-tm≡ = Hom.decode-mapCode≡

strictTm→approx
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ : Level}
    {K : Kernel ℓ ℓRel ℓCode₁}
    {K' : Kernel ℓ ℓRel ℓCode₂}
  → Tm≡ K K'
  → Surface.Tm≈ K K'
strictTm→approx = Hom.strict→approx

strictTm→under
  : ∀ {ℓ ℓRel ℓCode₁ ℓCode₂ : Level}
    {K : Kernel ℓ ℓRel ℓCode₁}
    {K' : Kernel ℓ ℓRel ℓCode₂}
  → Tm≡ K K'
  → Surface.Tm⊑ K K'
strictTm→under = Hom.strict→under
