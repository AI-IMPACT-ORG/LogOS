{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.DisplayedThin2Cat.MapDecorated where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.DisplayedThin2Cat.Core using (DisplayedThin2Cat; Ob; HomD)
open import LogOS.LT.DisplayedThin2Cat.Totalisation using
  ( TotalObj
  ; TotalThin2Cat
  ; mkTotalObjR
  ; mkTotalHomR
  ; base
  ; disp
  ; baseHom
  ; dispHom
  ; byBaseHom≡
  )

-- Functor that projects a decorated layer by object and hom projections.
mapDecorated
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj₁ ℓDHom₁ ℓDObj₂ ℓDHom₂}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (D₁ : DisplayedThin2Cat C ℓDObj₁ ℓDHom₁)
    (D₂ : DisplayedThin2Cat C ℓDObj₂ ℓDHom₂)
    (objMap : ∀ {A} → Ob D₁ A → Ob D₂ A)
    (homMap : ∀ {A B} {f : Con (Thin2Cat.Hom C A B)}
            {x : Ob D₁ A} {y : Ob D₁ B}
            → HomD D₁ f x y
            → HomD D₂ f (objMap x) (objMap y))
  → Thin2Functor (TotalThin2Cat D₁) (TotalThin2Cat D₂)
mapDecorated {C = C} D₁ D₂ objMap homMap =
  let
    module S = Thin2Cat (TotalThin2Cat D₁)
    module T = Thin2Cat (TotalThin2Cat D₂)
    mapObj' : TotalObj D₁ → TotalObj D₂
    mapObj' X = mkTotalObjR (base {D = D₁} X) (objMap (disp {D = D₁} X))
    mapHom' : ∀ {A B} → Con (S.Hom A B) → Con (T.Hom (mapObj' A) (mapObj' B))
    mapHom' {A} {B} h =
      let
        A₀ = base {D = D₁} A
        B₀ = base {D = D₁} B
        x₀ = disp {D = D₁} A
        y₀ = disp {D = D₁} B
      in
      mkTotalHomR
        (baseHom {C = C} {D = D₁} {X = A} {Y = B} h)
        (homMap
          {A = A₀} {B = B₀}
          {x = x₀} {y = y₀}
          (dispHom {D = D₁} h))
  in
  record
    { mapObj = mapObj'
    ; mapHom = mapHom'
    ; mapHom-mono = λ le → le
    ; id-pres = λ {A} →
        byBaseHom≡ {D = D₂} {X = mapObj' A} {Y = mapObj' A}
          (mapHom' (S.id {A = A}))
          (T.id {A = mapObj' A})
          refl
    ; comp-pres = λ {A} {B} {C₀} f g →
        byBaseHom≡ {D = D₂} {X = mapObj' A} {Y = mapObj' C₀}
          (mapHom' (S._∘_ f g))
          (mapHom' f T.∘ mapHom' g)
          refl
    }
