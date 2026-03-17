{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.Boundary2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Boundary-only base thin 2-category (G-tier spine).
--
-- Objects: kernels.
-- 1-cells: boundary morphisms `BoundaryHom` (monotone transport of constraints).
-- 2-cells: boundary-only refinements, defined as pullback along `transportView`
--          (pointwise on all boundary constraints), hence implementation-insensitive.
--
-- Design note:
-- This is the architectural base category. Implementation witnesses
-- (`mapCode` + coherence) are added separately as a displayed layer
-- (see `Implementation2Cat`).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con)
open import LogOS.LT.FunPreorder using (FunPreorder)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decode)
open import LogOS.LT.Thin2Cat using (Thin2Cat; Thin2CatLaws)
import LogOS.LT.Thin2Cat.Pointwise as Pointwise
import LogOS.LT.Thin2Cat.Pointwise.Strictification as PointwiseStrict
open import LogOS.LT.View using (View; μ; _⊑[_]_)

import LogOS.LT.BoundaryHom as Boundary

-- Level-aligned boundary morphisms (no content change).
--
-- `BoundaryHom K K'` does not mention `ℓCode`, but `LOG` hom-levels do, so we
-- `Lift` it to keep the ambient 2-category levels aligned with `LOG`.
BoundaryHomL
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Kernel ℓ ℓRel ℓCode → Kernel ℓ ℓRel ℓCode
  → Set (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode)
BoundaryHomL {ℓCode = ℓCode} K K' = Lift ℓCode (Boundary.BoundaryHom K K')

idBoundaryHomL
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
  → BoundaryHomL K K
idBoundaryHomL {ℓCode = ℓCode} {K = K} =
  lift {ℓ = ℓCode} (Boundary.idBoundaryHom K)

infixr 40 _∘ᴳ_
_∘ᴳ_
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K₁ K₂ K₃ : Kernel ℓ ℓRel ℓCode}
  → BoundaryHomL K₂ K₃ → BoundaryHomL K₁ K₂ → BoundaryHomL K₁ K₃
_∘ᴳ_ {ℓCode = ℓCode} g f =
  lift {ℓ = ℓCode} (Boundary._∘∂_ (lower g) (lower f))

map∂
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → BoundaryHomL K K'
  → Con (bnd K) → Con (bnd K')
map∂ h = Boundary.BoundaryHom.map∂ (lower h)

map∂-mono
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → (h : BoundaryHomL K K')
  → LogOS.Prelude.RefinementKit.MonoMap (bnd K) (bnd K') (map∂ h)
map∂-mono h = Boundary.BoundaryHom.map∂-mono (lower h)

map∂-∘ᴳ
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K₁ K₂ K₃ : Kernel ℓ ℓRel ℓCode}
    (g : BoundaryHomL K₂ K₃)
    (f : BoundaryHomL K₁ K₂)
    (c : Con (bnd K₁))
  → map∂ (g ∘ᴳ f) c ≡ map∂ g (map∂ f c)
map∂-∘ᴳ g f c = refl

-- Boundary-only observation transport: transport boundary constraints along `map∂`.
transportObs
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → BoundaryHomL K K'
  → Con (bnd K) → Con (bnd K')
transportObs h c = map∂ h c

transportView
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → View (BoundaryHomL K K') (FunPreorder (Con (bnd K)) (bnd K'))
transportView {K = K} {K' = K'} =
  record { μ = λ h c → transportObs {K = K} {K' = K'} h c }

-- Boundary-driven refinement between boundary morphisms.
infix 4 _⇒ᴳ_
_⇒ᴳ_
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
  → BoundaryHomL K K'
  → BoundaryHomL K K'
  → Set (ℓ ⊔ ℓRel)
_⇒ᴳ_ {K = K} {K' = K'} f g = f ⊑[ transportView {K = K} {K' = K'} ] g

whiskerLᴳ
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K₁ K₂ K₃ : Kernel ℓ ℓRel ℓCode}
  → (h : BoundaryHomL K₂ K₃)
  → {f g : BoundaryHomL K₁ K₂}
  → f ⇒ᴳ g
  → (h ∘ᴳ f) ⇒ᴳ (h ∘ᴳ g)
whiskerLᴳ {K₃ = K₃} h {f} {g} le c =
  subst
    (λ x → ConPreorder._⊑_ (bnd K₃) x (map∂ (h ∘ᴳ g) c))
    (sym (map∂-∘ᴳ h f c))
    (subst
      (λ y → ConPreorder._⊑_ (bnd K₃) (map∂ h (map∂ f c)) y)
      (sym (map∂-∘ᴳ h g c))
      (map∂-mono h (le c)))

whiskerRᴳ
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K₁ K₂ K₃ : Kernel ℓ ℓRel ℓCode}
    {f g : BoundaryHomL K₂ K₃}
  → (k : BoundaryHomL K₁ K₂)
  → f ⇒ᴳ g
  → (f ∘ᴳ k) ⇒ᴳ (g ∘ᴳ k)
whiskerRᴳ {K₃ = K₃} {f = f} {g = g} k le c =
  subst
    (λ x → ConPreorder._⊑_ (bnd K₃) x (map∂ (g ∘ᴳ k) c))
    (sym (map∂-∘ᴳ f k c))
    (subst
      (λ y → ConPreorder._⊑_ (bnd K₃) (map∂ f (map∂ k c)) y)
      (sym (map∂-∘ᴳ g k c))
      (le (map∂ k c)))

-- Specialise a boundary refinement `f ⇒ᴳ g` to decoded code observations.
restrict⇒ᴳ
  : ∀ {ℓ ℓRel ℓCode : Level}
    {K : Kernel ℓ ℓRel ℓCode}
    {K' : Kernel ℓ ℓRel ℓCode}
    {f g : BoundaryHomL K K'}
  → f ⇒ᴳ g
  → ∀ γ
  → ConPreorder._⊑_ (bnd K') (map∂ f (decode K γ)) (map∂ g (decode K γ))
restrict⇒ᴳ {K = K} fg γ = fg (decode K γ)

BoundaryHomPreorder
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Kernel ℓ ℓRel ℓCode → Kernel ℓ ℓRel ℓCode
  → ConPreorder (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode) (ℓ ⊔ ℓRel)
BoundaryHomPreorder {ℓ} {ℓRel} {ℓCode} =
  Pointwise.PointwiseHom
    (λ K → Con (bnd K))
    bnd
    BoundaryHomL
    transportObs

-- The boundary-only thin 2-category LOGᴳ.
LOGᴳ
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Cat
      (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
      (lsuc ℓ ⊔ lsuc ℓRel ⊔ ℓCode)
      (ℓ ⊔ ℓRel)
LOGᴳ {ℓ} {ℓRel} {ℓCode} =
  Pointwise.PointwiseThin2Cat
    (Kernel ℓ ℓRel ℓCode)
    (λ K → Con (bnd K))
    bnd
    BoundaryHomL
    transportObs
    idBoundaryHomL
    _∘ᴳ_
    (λ {A} {B} {C} {f} {f'} {g} le →
       whiskerRᴳ {f = f} {g = f'} g le)
    (λ {A} {B} {C} {f} {g} {g'} le →
       whiskerLᴳ f {f = g} {g = g'} le)

LOGᴳLaws : ∀ {ℓ ℓRel ℓCode : Level} → Thin2CatLaws (LOGᴳ {ℓ} {ℓRel} {ℓCode})
LOGᴳLaws {ℓ} {ℓRel} {ℓCode} =
  PointwiseStrict.PointwiseThin2CatLaws
    (Kernel ℓ ℓRel ℓCode)
    (λ K → Con (bnd K))
    bnd
    BoundaryHomL
    transportObs
    idBoundaryHomL
    _∘ᴳ_
    (λ {A} {B} {C} {f} {f'} {g} le →
       whiskerRᴳ {f = f} {g = f'} g le)
    (λ {A} {B} {C} {f} {g} {g'} le →
       whiskerLᴳ f {f = g} {g = g'} le)
    (λ _ _ → refl)
    (λ _ _ → refl)
    (λ _ _ _ _ → refl)
