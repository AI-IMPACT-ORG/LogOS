{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Thin2Cat where

open import LogOS.Prelude
open import LogOS.Minimal.Con

-- Thin 2-category (preorder-enriched category) interface.
--
-- This is meaning-only: it packages existing preorder structure without adding
-- new axioms to the kernel. Laws are recorded separately to avoid forcing
-- stronger commitments in core definitions.

record Thin2Cat (ℓObj ℓHom : Level) : Set (lsuc (ℓObj ⊔ ℓHom)) where
  infixr 9 _∘_
  field
    Obj : Set ℓObj
    Hom : Obj → Obj → ConPoset ℓHom

    id  : ∀ {A} → ConPoset.Con (Hom A A)
    _∘_ : ∀ {A B C}
        → ConPoset.Con (Hom B C)
        → ConPoset.Con (Hom A B)
        → ConPoset.Con (Hom A C)

    comp-mono-l
      : ∀ {A B C}
        {f f' : ConPoset.Con (Hom B C)}
        {g : ConPoset.Con (Hom A B)}
      → ConPoset._⊑_ (Hom B C) f f'
      → ConPoset._⊑_ (Hom A C) (f ∘ g) (f' ∘ g)

    comp-mono-r
      : ∀ {A B C}
        {f : ConPoset.Con (Hom B C)}
        {g g' : ConPoset.Con (Hom A B)}
      → ConPoset._⊑_ (Hom A B) g g'
      → ConPoset._⊑_ (Hom A C) (f ∘ g) (f ∘ g')

-- 2-category laws (as mutual refinement).
record Thin2CatLaws {ℓObj ℓHom}
                   (C : Thin2Cat ℓObj ℓHom)
                   : Set (lsuc (ℓObj ⊔ ℓHom)) where
  open Thin2Cat C
  field
    id-left
      : ∀ {A B} (f : ConPoset.Con (Hom A B))
      → _≈CP_ (Hom A B) (id ∘ f) f
    id-right
      : ∀ {A B} (f : ConPoset.Con (Hom A B))
      → _≈CP_ (Hom A B) (f ∘ id) f
    assoc
      : ∀ {A B C D}
        (f : ConPoset.Con (Hom C D))
        (g : ConPoset.Con (Hom B C))
        (h : ConPoset.Con (Hom A B))
      → _≈CP_ (Hom A D) ((f ∘ g) ∘ h) (f ∘ (g ∘ h))

-- In a thin 2-category, 2-cells are preorder proofs. Horizontal composition
-- is just monotonicity in both arguments; vertical composition is `trans`.

comp-mono
  : ∀ {ℓObj ℓHom}
    {C : Thin2Cat ℓObj ℓHom}
    {A B C' : Thin2Cat.Obj C}
    {f f' : ConPoset.Con (Thin2Cat.Hom C B C')}
    {g g' : ConPoset.Con (Thin2Cat.Hom C A B)}
  → ConPoset._⊑_ (Thin2Cat.Hom C B C') f f'
  → ConPoset._⊑_ (Thin2Cat.Hom C A B) g g'
  → ConPoset._⊑_ (Thin2Cat.Hom C A C') (Thin2Cat._∘_ C f g)
                                       (Thin2Cat._∘_ C f' g')
comp-mono {C = C} {A} {B} {C' = C'} {f = f} {f' = f'} f≤f' g≤g' =
  let
    step₁ = Thin2Cat.comp-mono-l C f≤f'
    step₂ = Thin2Cat.comp-mono-r C {f = f'} g≤g'
  in
  ConPoset.trans (Thin2Cat.Hom C A C') step₁ step₂

-- Whiskering (2-cell transport) is immediate from monotonicity.

whisker-left
  : ∀ {ℓObj ℓHom}
    {C : Thin2Cat ℓObj ℓHom}
    {A B C' : Thin2Cat.Obj C}
    {f f' : ConPoset.Con (Thin2Cat.Hom C B C')}
    {g : ConPoset.Con (Thin2Cat.Hom C A B)}
  → ConPoset._⊑_ (Thin2Cat.Hom C B C') f f'
  → ConPoset._⊑_ (Thin2Cat.Hom C A C') (Thin2Cat._∘_ C f g)
                                       (Thin2Cat._∘_ C f' g)
whisker-left {C = C} = Thin2Cat.comp-mono-l C

whisker-right
  : ∀ {ℓObj ℓHom}
    {C : Thin2Cat ℓObj ℓHom}
    {A B C' : Thin2Cat.Obj C}
    {f : ConPoset.Con (Thin2Cat.Hom C B C')}
    {g g' : ConPoset.Con (Thin2Cat.Hom C A B)}
  → ConPoset._⊑_ (Thin2Cat.Hom C A B) g g'
  → ConPoset._⊑_ (Thin2Cat.Hom C A C') (Thin2Cat._∘_ C f g)
                                       (Thin2Cat._∘_ C f g')
whisker-right {C = C} = Thin2Cat.comp-mono-r C
