{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.BoundaryDecode2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Boundary-only decoded refinement skeleton (G-tier 1-cells, LOG-style 2-cell predicate).
--
-- Objects: kernels
-- 1-cells: boundary morphisms (`BoundaryHomL`)
-- 2-cells (predicate): decoded-only refinement on the transported decode
--   `∀ γ : Code K, map∂ f (decode γ) ⊑ map∂ g (decode γ)`
--
-- Important:
-- this decoded-only refinement is *not stable under precomposition* for arbitrary
-- boundary morphisms, because there is no way to transport codes without an
-- explicit implementation witness (`mapCode`). Therefore this module does **not** define a
-- `Thin2Cat`. The corresponding thin 2-category is `LOG` (where 1-cells carry
-- `mapCode`) and `LOGᴳ` (where 2-cells quantify over all boundary constraints).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode)
import LogOS.LT.Thin2Cat.Pointwise as Pointwise

import LogOS.LT.BoundaryHom as Boundary
open import LogOS.LT.LOG.Boundary2Cat using
  ( BoundaryHomL
  ; map∂
  ; map∂-mono
  ; _∘ᴳ_
  ; _⇒ᴳ_
  ; restrict⇒ᴳ
  )

infix 4 _⇒ᵈ_
_⇒ᵈ_
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → BoundaryHomL K K'
  → BoundaryHomL K K'
  → Set (ℓCode ⊔ ℓRel)
_⇒ᵈ_ {K = K} {K' = K'} f g =
  ∀ γ → _⊑_ (bnd K') (map∂ f (decode K γ)) (map∂ g (decode K γ))

BoundaryDecodePreorder
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Kernel ℓ ℓRel ℓCode
  → Kernel ℓ ℓRel ℓCode
  → ConPreorder (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode) (ℓCode ⊔ ℓRel)
BoundaryDecodePreorder {ℓ} {ℓRel} {ℓCode} K K' =
  Pointwise.PointwisePreorder
    (BoundaryHomL K K')
    (Code K)
    (bnd K')
    (λ h γ → map∂ h (decode K γ))

whiskerRᵈ
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K₁ K₂ K₃ : Kernel ℓ ℓRel ℓCode}
    {f g : BoundaryHomL K₁ K₂}
  → (k : BoundaryHomL K₂ K₃)
  → f ⇒ᵈ g
  → (k ∘ᴳ f) ⇒ᵈ (k ∘ᴳ g)
whiskerRᵈ k fg γ = map∂-mono k (fg γ)

restrict⇒ᴳ→⇒ᵈ
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
    {f g : BoundaryHomL K K'}
  → f ⇒ᴳ g
  → f ⇒ᵈ g
restrict⇒ᴳ→⇒ᵈ {K = K} {K' = K'} {f = f} {g = g} fg γ =
  restrict⇒ᴳ {K = K} {K' = K'} {f = f} {g = g} fg γ
