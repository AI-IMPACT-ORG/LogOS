{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Thin2Cat.Pointwise.Strictification where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Strict observation equalities yielding refinement laws for pointwise thin
-- 2-categories.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_)
open import LogOS.LT.Thin2Cat using (Thin2CatLaws)
open import LogOS.LT.Thin2Cat.Pointwise using
  ( PointwiseHom
  ; PointwiseThin2Cat
  ; pointwise≈-from-obs≡
  )

PointwiseThin2CatLaws
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
    (obs-id-left :
      ∀ {A B}
      → (f : Hom₀ A B)
      → (x : Point A)
      → obs (_∘₀_ id₀ f) x ≡ obs f x)
    (obs-id-right :
      ∀ {A B}
      → (f : Hom₀ A B)
      → (x : Point A)
      → obs (_∘₀_ f id₀) x ≡ obs f x)
    (obs-assoc :
      ∀ {A B C D}
      → (f : Hom₀ C D)
      → (g : Hom₀ B C)
      → (h : Hom₀ A B)
      → (x : Point A)
      → obs (_∘₀_ (_∘₀_ f g) h) x ≡ obs (_∘₀_ f (_∘₀_ g h)) x)
  → Thin2CatLaws
      (PointwiseThin2Cat Obj Point CP Hom₀ obs id₀ _∘₀_ comp-mono-l₀ comp-mono-r₀)
PointwiseThin2CatLaws Obj Point CP Hom₀ obs id₀ _∘₀_ comp-mono-l₀ comp-mono-r₀ obs-id-left obs-id-right obs-assoc =
  record
    { id-left = λ {A} {B} f →
        pointwise≈-from-obs≡
          {H = Hom₀ A B}
          {X = Point A}
          {CP = CP B}
          {obs = λ h x → obs h x}
          {f = _∘₀_ id₀ f}
          {g = f}
          (obs-id-left f)
    ; id-right = λ {A} {B} f →
        pointwise≈-from-obs≡
          {H = Hom₀ A B}
          {X = Point A}
          {CP = CP B}
          {obs = λ h x → obs h x}
          {f = _∘₀_ f id₀}
          {g = f}
          (obs-id-right f)
    ; assoc = λ {A} {B} {C} {D} f g h →
        pointwise≈-from-obs≡
          {H = Hom₀ A D}
          {X = Point A}
          {CP = CP D}
          {obs = λ k x → obs k x}
          {f = _∘₀_ (_∘₀_ f g) h}
          {g = _∘₀_ f (_∘₀_ g h)}
          (obs-assoc f g h)
    }
