{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.DisplayedThin2Cat.Product where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; _≈_; ≈-refl)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.DisplayedThin2Cat.Core using (DisplayedThin2Cat; Ob; HomD; idD; compD)
open import LogOS.LT.DisplayedThin2Cat.Totalisation using
  ( TotalObj
  ; TotalThin2Cat
  ; TotalHom
  ; mkTotalObjR
  ; mkTotalHomR
  ; base
  ; disp
  ; baseHom
  ; dispHom
  )

-- --------------------------------------------------------------------------
-- Product of displayed structures over the same base.

ProductDisplayed
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj₁ ℓDHom₁ ℓDObj₂ ℓDHom₂}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → DisplayedThin2Cat C ℓDObj₁ ℓDHom₁
  → DisplayedThin2Cat C ℓDObj₂ ℓDHom₂
  → DisplayedThin2Cat C (ℓDObj₁ ⊔ ℓDObj₂) (ℓDHom₁ ⊔ ℓDHom₂)
ProductDisplayed {C = C} D₁ D₂ =
  let module B = Thin2Cat C in
  record
    { Ob = λ A → Ob D₁ A × Ob D₂ A
    ; HomD = λ {A} {B₀} (f : Con (B.Hom A B₀)) x y →
        HomD D₁ f (fst x) (fst y) × HomD D₂ f (snd x) (snd y)
    ; idD = λ {A} x → idD D₁ (fst x) , idD D₂ (snd x)
    ; compD =
        λ {A} {B₀} {C₀} {f} {g} {x} {y} {z} fx gy →
          ( compD D₁ (fst fx) (fst gy)
          , compD D₂ (snd fx) (snd gy)
          )
    }

-- Terminology alias (for readers coming from “displayed categories”):
-- this is exactly displayed-object + displayed-arrow data, specialised to a
-- locally preordered base.
DisplayedCat = DisplayedThin2Cat

forgetProductLeft
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj₁ ℓDHom₁ ℓDObj₂ ℓDHom₂}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (D₁ : DisplayedThin2Cat C ℓDObj₁ ℓDHom₁)
    (D₂ : DisplayedThin2Cat C ℓDObj₂ ℓDHom₂)
  → Thin2Functor
      (TotalThin2Cat (ProductDisplayed D₁ D₂))
      (TotalThin2Cat D₁)
forgetProductLeft {C = C} D₁ D₂ =
  let
    module T = Thin2Cat (TotalThin2Cat D₁)
    module S = Thin2Cat (TotalThin2Cat (ProductDisplayed D₁ D₂))
    D₁₂ = ProductDisplayed D₁ D₂
    mapObj' : TotalObj D₁₂ → TotalObj D₁
    mapObj' X = mkTotalObjR (base {D = D₁₂} X) (fst (disp {D = D₁₂} X))
    mapHom' : ∀ {A B} → Con (S.Hom A B) → Con (T.Hom (mapObj' A) (mapObj' B))
    mapHom' f = mkTotalHomR (baseHom {D = D₁₂} f) (fst (dispHom {D = D₁₂} f))
  in
  record
    { mapObj = mapObj'
    ; mapHom = mapHom'
    ; mapHom-mono = λ le → le
    ; id-pres = λ {A} →
        ≈-refl (T.Hom (mapObj' A) (mapObj' A)) (T.id {A = mapObj' A})
    ; comp-pres = λ {A} {B₀} {C₀} f g →
        ≈-refl (T.Hom (mapObj' A) (mapObj' C₀)) (mapHom' (f S.∘ g))
    }

forgetProductRight
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj₁ ℓDHom₁ ℓDObj₂ ℓDHom₂}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (D₁ : DisplayedThin2Cat C ℓDObj₁ ℓDHom₁)
    (D₂ : DisplayedThin2Cat C ℓDObj₂ ℓDHom₂)
  → Thin2Functor
      (TotalThin2Cat (ProductDisplayed D₁ D₂))
      (TotalThin2Cat D₂)
forgetProductRight {C = C} D₁ D₂ =
  let
    module T = Thin2Cat (TotalThin2Cat D₂)
    module S = Thin2Cat (TotalThin2Cat (ProductDisplayed D₁ D₂))
    D₁₂ = ProductDisplayed D₁ D₂
    mapObj' : TotalObj D₁₂ → TotalObj D₂
    mapObj' X = mkTotalObjR (base {D = D₁₂} X) (snd (disp {D = D₁₂} X))
    mapHom' : ∀ {A B} → Con (S.Hom A B) → Con (T.Hom (mapObj' A) (mapObj' B))
    mapHom' f = mkTotalHomR (baseHom {D = D₁₂} f) (snd (dispHom {D = D₁₂} f))
  in
  record
    { mapObj = mapObj'
    ; mapHom = mapHom'
    ; mapHom-mono = λ le → le
    ; id-pres = λ {A} →
        ≈-refl (T.Hom (mapObj' A) (mapObj' A)) (T.id {A = mapObj' A})
    ; comp-pres = λ {A} {B₀} {C₀} f g →
        ≈-refl (T.Hom (mapObj' A) (mapObj' C₀)) (mapHom' (f S.∘ g))
    }
