{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Thin2Cat.Pointwise where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Generic pointwise refinement builders for thin 2-categorical homs.
--
-- This module factors out the recurring pattern:
-- - choose a hom carrier `H`,
-- - choose a point domain `X`,
-- - observe each hom at each point into one target preorder `CP`,
-- - compare homs pointwise in `CP`.
--
-- The LOG family uses this pattern repeatedly:
-- boundary transport, decoded transport, and guarded/boundary-only variants all
-- differ only in the observation map.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; MonoMap)
open import LogOS.LT.Thin2Cat using (Thin2Cat; Thin2CatLaws)

PointwiseRel
  : ∀ {ℓH ℓX ℓCon ℓRel}
    {H : Set ℓH}
  → (X : Set ℓX)
  → (CP : ConPreorder ℓCon ℓRel)
  → (obs : H → X → Con CP)
  → H → H → Set (ℓX ⊔ ℓRel)
PointwiseRel X CP obs f g = ∀ x → _⊑_ CP (obs f x) (obs g x)

PointwisePreorder
  : ∀ {ℓH ℓX ℓCon ℓRel}
  → (H : Set ℓH)
  → (X : Set ℓX)
  → (CP : ConPreorder ℓCon ℓRel)
  → (obs : H → X → Con CP)
  → ConPreorder ℓH (ℓX ⊔ ℓRel)
PointwisePreorder H X CP obs =
  record
    { Con = H
    ; _⊑_ = PointwiseRel X CP obs
    ; refl = λ {f} x → ConPreorder.refl CP
    ; trans = λ {f} {g} {h} fg gh x →
        let
          module R = LogOS.Prelude.RefinementKit.Reasoning CP
        in
        R._⊑⟨_⟩_ (obs f x) (fg x) (gh x)
    }

PointwiseHom
  : ∀ {ℓObj ℓPoint ℓHom ℓCon ℓRel}
    {Obj : Set ℓObj}
  → (Point : Obj → Set ℓPoint)
  → (CP : Obj → ConPreorder ℓCon ℓRel)
  → (Hom₀ : Obj → Obj → Set ℓHom)
  → (obs : ∀ {A B} → Hom₀ A B → Point A → Con (CP B))
  → Obj → Obj → ConPreorder ℓHom (ℓPoint ⊔ ℓRel)
PointwiseHom Point CP Hom₀ obs A B =
  PointwisePreorder (Hom₀ A B) (Point A) (CP B) (obs {A} {B})

whiskerR-by-pre
  : ∀ {ℓH ℓX ℓY ℓCon ℓRel}
    {H : Set ℓH}
    {X : Set ℓX}
    {Y : Set ℓY}
    {CP : ConPreorder ℓCon ℓRel}
    (obs : H → Y → Con CP)
    (pre : X → Y)
    {f g : H}
  → PointwiseRel Y CP obs f g
  → PointwiseRel X CP (λ h x → obs h (pre x)) f g
whiskerR-by-pre obs pre fg x = fg (pre x)

whiskerL-by-post
  : ∀ {ℓH ℓX ℓCon₁ ℓRel₁ ℓCon₂ ℓRel₂}
    {H : Set ℓH}
    {X : Set ℓX}
    {CP₁ : ConPreorder ℓCon₁ ℓRel₁}
    {CP₂ : ConPreorder ℓCon₂ ℓRel₂}
    (obs : H → X → Con CP₁)
    (post : Con CP₁ → Con CP₂)
  → MonoMap CP₁ CP₂ post
  → {f g : H}
  → PointwiseRel X CP₁ obs f g
  → PointwiseRel X CP₂ (λ h x → post (obs h x)) f g
whiskerL-by-post obs post post-mono fg x = post-mono (fg x)

PointwiseThin2Cat
  : ∀ {ℓObj ℓPoint ℓHom ℓCon ℓRel}
    (Obj : Set ℓObj)
    (Point : Obj → Set ℓPoint)
    (CP : Obj → ConPreorder ℓCon ℓRel)
    (Hom₀ : Obj → Obj → Set ℓHom)
    (obs : ∀ {A B} → Hom₀ A B → Point A → Con (CP B))
    (id₀ : ∀ {A} → Hom₀ A A)
    (_∘₀_ : ∀ {A B C} → Hom₀ B C → Hom₀ A B → Hom₀ A C)
    (comp-mono-l₀ :
      ∀ {A B C}
        {f f' : Hom₀ B C}
        {g : Hom₀ A B}
      → _⊑_ (PointwiseHom Point CP Hom₀ obs B C) f f'
      → _⊑_ (PointwiseHom Point CP Hom₀ obs A C) (_∘₀_ f g) (_∘₀_ f' g))
    (comp-mono-r₀ :
      ∀ {A B C}
        {f : Hom₀ B C}
        {g g' : Hom₀ A B}
      → _⊑_ (PointwiseHom Point CP Hom₀ obs A B) g g'
      → _⊑_ (PointwiseHom Point CP Hom₀ obs A C) (_∘₀_ f g) (_∘₀_ f g'))
  → Thin2Cat ℓObj ℓHom (ℓPoint ⊔ ℓRel)
PointwiseThin2Cat Obj Point CP Hom₀ obs id₀ _∘₀_ comp-mono-l₀ comp-mono-r₀ =
  record
    { Obj = Obj
    ; Hom = PointwiseHom Point CP Hom₀ obs
    ; id = id₀
    ; _∘_ = _∘₀_
    ; comp-mono-l = comp-mono-l₀
    ; comp-mono-r = comp-mono-r₀
    }

pointwise≈-from-obs≡
  : ∀ {ℓH ℓX ℓCon ℓRel}
    {H : Set ℓH}
    {X : Set ℓX}
    {CP : ConPreorder ℓCon ℓRel}
    {obs : H → X → Con CP}
    {f g : H}
  → (∀ x → obs f x ≡ obs g x)
  → _≈_ (PointwisePreorder H X CP obs) f g
pointwise≈-from-obs≡ {CP = CP} {obs = obs} {f = f} {g = g} eq =
  ( left
  , right
  )
  where
    left : ∀ x → _⊑_ CP (obs f x) (obs g x)
    left x rewrite eq x = ConPreorder.refl CP

    right : ∀ x → _⊑_ CP (obs g x) (obs f x)
    right x rewrite sym (eq x) = ConPreorder.refl CP
