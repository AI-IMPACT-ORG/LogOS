{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.DisplayedThin2Cat.Strictification where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using
  ( Thin2Functor
  ; mapObj
  ; mapHom
  ; mapHom-mono
  )
open import LogOS.LT.Thin2Functor.Strictification using (StrictThin2Functor)
open import LogOS.LT.DisplayedThin2Cat.Core using
  ( DisplayedThin2Cat
  ; Ob
  ; HomD
  ; idD
  ; compD
  )
open import LogOS.LT.DisplayedThin2Cat.Totalisation using
  ( DecoratedThin2Cat
  ; DecoratedObj
  ; mkTotalObjR
  ; mkTotalHomR
  ; base
  ; disp
  ; baseHom
  ; dispHom
  ; byBaseHom≡
  )

reindexDisplayedStrict
  : ∀ {ℓObj₁ ℓHomCon₁ ℓHomRel₁ ℓObj₂ ℓHomCon₂ ℓHomRel₂ ℓDObj ℓDHom}
    {C₁ : Thin2Cat ℓObj₁ ℓHomCon₁ ℓHomRel₁}
    {C₂ : Thin2Cat ℓObj₂ ℓHomCon₂ ℓHomRel₂}
  → (F : Thin2Functor C₁ C₂)
  → (D : DisplayedThin2Cat C₂ ℓDObj ℓDHom)
  → (id-pres≡
      : ∀ {A}
      → mapHom F {A = A} {B = A} (Thin2Cat.id C₁ {A = A})
        ≡ Thin2Cat.id C₂ {A = mapObj F A})
  → (comp-pres≡
      : ∀ {A B C}
        (f : Con (Thin2Cat.Hom C₁ B C))
        (g : Con (Thin2Cat.Hom C₁ A B))
      → mapHom F {A = A} {B = C} (Thin2Cat._∘_ C₁ {A = A} {B = B} {C = C} f g)
        ≡ Thin2Cat._∘_ C₂
            {A = mapObj F A}
            {B = mapObj F B}
            {C = mapObj F C}
            (mapHom F {A = B} {B = C} f)
            (mapHom F {A = A} {B = B} g))
  → DisplayedThin2Cat C₁ ℓDObj ℓDHom
reindexDisplayedStrict {C₁ = C₁} {C₂ = C₂} F D id-pres≡ comp-pres≡ =
  record
    { Ob = λ A → Ob D (mapObj F A)
    ; HomD = λ {A} {B} f x y → HomD D (mapHom F {A = A} {B = B} f) x y
    ; idD = λ {A} x →
        subst (λ hom → HomD D hom x x)
          (sym (id-pres≡ {A = A}))
          (idD D x)
    ; compD = λ {A} {B} {C} {f} {g} {x} {y} {z} hf hg →
        subst (λ hom → HomD D hom x z)
          (sym (comp-pres≡ {A = A} {B = B} {C = C} g f))
          (compD D hf hg)
    }

reindexDisplayedStrictF
  : ∀ {ℓObj₁ ℓHomCon₁ ℓHomRel₁ ℓObj₂ ℓHomCon₂ ℓHomRel₂ ℓDObj ℓDHom}
    {C₁ : Thin2Cat ℓObj₁ ℓHomCon₁ ℓHomRel₁}
    {C₂ : Thin2Cat ℓObj₂ ℓHomCon₂ ℓHomRel₂}
  → StrictThin2Functor C₁ C₂
  → DisplayedThin2Cat C₂ ℓDObj ℓDHom
  → DisplayedThin2Cat C₁ ℓDObj ℓDHom
reindexDisplayedStrictF SF D =
  reindexDisplayedStrict
    (StrictThin2Functor.F SF)
    D
    (StrictThin2Functor.id-pres≡ SF)
    (StrictThin2Functor.comp-pres≡ SF)

weakenReindexDisplayedStrictF
  : ∀ {ℓObj₁ ℓHomCon₁ ℓHomRel₁ ℓObj₂ ℓHomCon₂ ℓHomRel₂ ℓDObj ℓDHom}
    {C₁ : Thin2Cat ℓObj₁ ℓHomCon₁ ℓHomRel₁}
    {C₂ : Thin2Cat ℓObj₂ ℓHomCon₂ ℓHomRel₂}
  → (SF : StrictThin2Functor C₁ C₂)
  → (D : DisplayedThin2Cat C₂ ℓDObj ℓDHom)
  → Thin2Functor
      (DecoratedThin2Cat (reindexDisplayedStrictF SF D))
      (DecoratedThin2Cat D)
weakenReindexDisplayedStrictF {C₁ = C₁} {C₂ = C₂} SF D =
  let
    F = StrictThin2Functor.F SF
    D₁ = reindexDisplayedStrictF SF D

    module Src = Thin2Cat (DecoratedThin2Cat D₁)
    module Tgt = Thin2Cat (DecoratedThin2Cat D)

    mapObj′ : DecoratedObj D₁ → DecoratedObj D
    mapObj′ X = mkTotalObjR (mapObj F (base {D = D₁} X)) (disp {D = D₁} X)

    mapHom′
      : ∀ {A B}
      → Con (Src.Hom A B)
      → Con (Tgt.Hom (mapObj′ A) (mapObj′ B))
    mapHom′ {A} {B} h =
      mkTotalHomR
        (mapHom F {A = base {D = D₁} A} {B = base {D = D₁} B}
          (baseHom {D = D₁} {X = A} {Y = B} h))
        (dispHom {D = D₁} {X = A} {Y = B} h)
    in
  record
    { mapObj = mapObj′
    ; mapHom = λ {A} {B} h → mapHom′ {A = A} {B = B} h
    ; mapHom-mono =
        λ {A} {B} {f} {g} le →
          mapHom-mono F {A = base {D = D₁} A} {B = base {D = D₁} B} le
    ; id-pres = λ {A} →
        byBaseHom≡ {D = D} {X = mapObj′ A} {Y = mapObj′ A}
          (mapHom′ {A = A} {B = A} (Src.id {A = A}))
          (Tgt.id {A = mapObj′ A})
          (StrictThin2Functor.id-pres≡ SF {A = base {D = D₁} A})
    ; comp-pres = λ {A} {B} {C} f g →
        byBaseHom≡ {D = D} {X = mapObj′ A} {Y = mapObj′ C}
          (mapHom′ {A = A} {B = C} (Src._∘_ {A = A} {B = B} {C = C} f g))
          (mapHom′ {A = B} {B = C} f Tgt.∘ mapHom′ {A = A} {B = B} g)
          (StrictThin2Functor.comp-pres≡ SF
            {A = base {D = D₁} A}
            {B = base {D = D₁} B}
            {C₀ = base {D = D₁} C}
            (baseHom {D = D₁} {X = B} {Y = C} f)
            (baseHom {D = D₁} {X = A} {Y = B} g))
    }
