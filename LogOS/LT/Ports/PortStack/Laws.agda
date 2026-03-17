{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Ports.PortStack.Laws where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; _≈_)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (mapObj; mapHom; id-pres; comp-pres)
open import LogOS.LT.Ports.PortStack.Raw using
  ( PortStack
  ; StackCat
  ; Substack
  ; baseObj
  ; baseHom
  ; forgetStack
  ; forgetSubstack
  )

forgetStack-id≈
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (S : PortStack C)
    {A}
  → _≈_
      (Thin2Cat.Hom C (baseObj {C = C} {S = S} A) (baseObj {C = C} {S = S} A))
      (mapHom (forgetStack S) (Thin2Cat.id (StackCat S) {A}))
      (Thin2Cat.id C)
forgetStack-id≈ S {A = A} = id-pres (forgetStack S) {A = A}

baseHom-id≈
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (S : PortStack C)
    {A}
  → _≈_
      (Thin2Cat.Hom C (baseObj {C = C} {S = S} A) (baseObj {C = C} {S = S} A))
      (baseHom {C = C} {S = S} (Thin2Cat.id (StackCat S) {A}))
      (Thin2Cat.id C)
baseHom-id≈ S {A = A} = forgetStack-id≈ S {A = A}

forgetStack-comp≈
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (S : PortStack C)
    {A B C₀}
    (f : Con (Thin2Cat.Hom (StackCat S) B C₀))
    (g : Con (Thin2Cat.Hom (StackCat S) A B))
  → _≈_
      (Thin2Cat.Hom C (baseObj {C = C} {S = S} A) (baseObj {C = C} {S = S} C₀))
      (mapHom (forgetStack S) (Thin2Cat._∘_ (StackCat S) f g))
      (Thin2Cat._∘_ C
        (mapHom (forgetStack S) f)
        (mapHom (forgetStack S) g))
forgetStack-comp≈ S {A = A} {B = B} {C₀ = C₀} =
  comp-pres (forgetStack S) {A = A} {B = B} {C₀ = C₀}

baseHom-comp≈
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (S : PortStack C)
    {A B C₀}
    (f : Con (Thin2Cat.Hom (StackCat S) B C₀))
    (g : Con (Thin2Cat.Hom (StackCat S) A B))
  → _≈_
      (Thin2Cat.Hom C (baseObj {C = C} {S = S} A) (baseObj {C = C} {S = S} C₀))
      (baseHom {C = C} {S = S} (Thin2Cat._∘_ (StackCat S) f g))
      (Thin2Cat._∘_ C
        (baseHom {C = C} {S = S} f)
        (baseHom {C = C} {S = S} g))
baseHom-comp≈ S {A = A} {B = B} {C₀ = C₀} f g =
  forgetStack-comp≈ S {A = A} {B = B} {C₀ = C₀} f g

forgetSubstack-id≈
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Y X : PortStack C}
    (p : Substack Y X)
    {A}
  → _≈_
      (Thin2Cat.Hom (StackCat Y) (mapObj (forgetSubstack p) A) (mapObj (forgetSubstack p) A))
      (mapHom (forgetSubstack p) (Thin2Cat.id (StackCat X) {A}))
      (Thin2Cat.id (StackCat Y))
forgetSubstack-id≈ p {A = A} = id-pres (forgetSubstack p) {A = A}

forgetSubstack-comp≈
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Y X : PortStack C}
    (p : Substack Y X)
    {A B C₀}
    (f : Con (Thin2Cat.Hom (StackCat X) B C₀))
    (g : Con (Thin2Cat.Hom (StackCat X) A B))
  → _≈_
      (Thin2Cat.Hom (StackCat Y) (mapObj (forgetSubstack p) A) (mapObj (forgetSubstack p) C₀))
      (mapHom (forgetSubstack p) (Thin2Cat._∘_ (StackCat X) f g))
      (Thin2Cat._∘_ (StackCat Y)
        (mapHom (forgetSubstack p) f)
        (mapHom (forgetSubstack p) g))
forgetSubstack-comp≈ p {A = A} {B = B} {C₀ = C₀} =
  comp-pres (forgetSubstack p) {A = A} {B = B} {C₀ = C₀}
