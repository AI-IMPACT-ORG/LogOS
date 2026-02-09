{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.RelThin2Cat where

-- RelPreorder-enriched category (thin 2-category) interface.
--
-- This generalizes `LogOS.Minimal.Thin2Cat` to the two-level preorder setting
-- (`RelPreorder`), so observational relations can be used as 2-cells without
-- universe-lifting tricks.

open import LogOS.Prelude

open import LogOS.Minimal.RelPreorder as RP using (RelPreorder; _≈RP_)

record RelThin2Cat (ℓObj ℓHom ℓ₂ : Level) : Set (lsuc (ℓObj ⊔ ℓHom ⊔ ℓ₂)) where
  infixr 9 _∘_
  field
    Obj : Set ℓObj
    Hom : Obj → Obj → RelPreorder ℓHom ℓ₂

    id  : ∀ {A} → RelPreorder.Con (Hom A A)
    _∘_ : ∀ {A B C}
        → RelPreorder.Con (Hom B C)
        → RelPreorder.Con (Hom A B)
        → RelPreorder.Con (Hom A C)

    comp-mono-l
      : ∀ {A B C}
        {f f' : RelPreorder.Con (Hom B C)}
        {g : RelPreorder.Con (Hom A B)}
      → RelPreorder._⊑_ (Hom B C) f f'
      → RelPreorder._⊑_ (Hom A C) (f ∘ g) (f' ∘ g)

    comp-mono-r
      : ∀ {A B C}
        {f : RelPreorder.Con (Hom B C)}
        {g g' : RelPreorder.Con (Hom A B)}
      → RelPreorder._⊑_ (Hom A B) g g'
      → RelPreorder._⊑_ (Hom A C) (f ∘ g) (f ∘ g')

record RelThin2CatLaws
  {ℓObj ℓHom ℓ₂}
  (C : RelThin2Cat ℓObj ℓHom ℓ₂)
  : Set (lsuc (ℓObj ⊔ ℓHom ⊔ ℓ₂)) where
  open RelThin2Cat C
  field
    id-left
      : ∀ {A B} (f : RelPreorder.Con (Hom A B))
      → _≈RP_ (Hom A B) (id ∘ f) f
    id-right
      : ∀ {A B} (f : RelPreorder.Con (Hom A B))
      → _≈RP_ (Hom A B) (f ∘ id) f
    assoc
      : ∀ {A B C D}
        (f : RelPreorder.Con (Hom C D))
        (g : RelPreorder.Con (Hom B C))
        (h : RelPreorder.Con (Hom A B))
      → _≈RP_ (Hom A D) ((f ∘ g) ∘ h) (f ∘ (g ∘ h))

-- Derived helper: composition monotone in both arguments.
comp-mono
  : ∀ {ℓObj ℓHom ℓ₂}
    {C : RelThin2Cat ℓObj ℓHom ℓ₂}
    {A B C' : RelThin2Cat.Obj C}
    {f f' : RelPreorder.Con (RelThin2Cat.Hom C B C')}
    {g g' : RelPreorder.Con (RelThin2Cat.Hom C A B)}
  → RelPreorder._⊑_ (RelThin2Cat.Hom C B C') f f'
  → RelPreorder._⊑_ (RelThin2Cat.Hom C A B) g g'
  → RelPreorder._⊑_ (RelThin2Cat.Hom C A C')
      (RelThin2Cat._∘_ C f g)
      (RelThin2Cat._∘_ C f' g')
comp-mono {C = C} {A} {B} {C' = C'} {f = f} {f' = f'} f≤f' g≤g' =
  let
    step₁ = RelThin2Cat.comp-mono-l C f≤f'
    step₂ = RelThin2Cat.comp-mono-r C {f = f'} g≤g'
  in
  RelPreorder.trans (RelThin2Cat.Hom C A C') step₁ step₂

whisker-left
  : ∀ {ℓObj ℓHom ℓ₂}
    {C : RelThin2Cat ℓObj ℓHom ℓ₂}
    {A B C' : RelThin2Cat.Obj C}
    {f f' : RelPreorder.Con (RelThin2Cat.Hom C B C')}
    {g : RelPreorder.Con (RelThin2Cat.Hom C A B)}
  → RelPreorder._⊑_ (RelThin2Cat.Hom C B C') f f'
  → RelPreorder._⊑_ (RelThin2Cat.Hom C A C')
      (RelThin2Cat._∘_ C f g)
      (RelThin2Cat._∘_ C f' g)
whisker-left {C = C} = RelThin2Cat.comp-mono-l C

whisker-right
  : ∀ {ℓObj ℓHom ℓ₂}
    {C : RelThin2Cat ℓObj ℓHom ℓ₂}
    {A B C' : RelThin2Cat.Obj C}
    {f : RelPreorder.Con (RelThin2Cat.Hom C B C')}
    {g g' : RelPreorder.Con (RelThin2Cat.Hom C A B)}
  → RelPreorder._⊑_ (RelThin2Cat.Hom C A B) g g'
  → RelPreorder._⊑_ (RelThin2Cat.Hom C A C')
      (RelThin2Cat._∘_ C f g)
      (RelThin2Cat._∘_ C f g')
whisker-right {C = C} = RelThin2Cat.comp-mono-r C
