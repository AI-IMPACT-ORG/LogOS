{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
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
    Hom : Obj → Obj → ConPreorder ℓHom

    id  : ∀ {A} → ConPreorder.Con (Hom A A)
    _∘_ : ∀ {A B C}
        → ConPreorder.Con (Hom B C)
        → ConPreorder.Con (Hom A B)
        → ConPreorder.Con (Hom A C)

    comp-mono-l
      : ∀ {A B C}
        {f f' : ConPreorder.Con (Hom B C)}
        {g : ConPreorder.Con (Hom A B)}
      → ConPreorder._⊑_ (Hom B C) f f'
      → ConPreorder._⊑_ (Hom A C) (f ∘ g) (f' ∘ g)

    comp-mono-r
      : ∀ {A B C}
        {f : ConPreorder.Con (Hom B C)}
        {g g' : ConPreorder.Con (Hom A B)}
      → ConPreorder._⊑_ (Hom A B) g g'
      → ConPreorder._⊑_ (Hom A C) (f ∘ g) (f ∘ g')

-- 2-category laws (as mutual refinement).
record Thin2CatLaws {ℓObj ℓHom}
                   (C : Thin2Cat ℓObj ℓHom)
                   : Set (lsuc (ℓObj ⊔ ℓHom)) where
  open Thin2Cat C
  field
    id-left
      : ∀ {A B} (f : ConPreorder.Con (Hom A B))
      → _≈CP_ (Hom A B) (id ∘ f) f
    id-right
      : ∀ {A B} (f : ConPreorder.Con (Hom A B))
      → _≈CP_ (Hom A B) (f ∘ id) f
    assoc
      : ∀ {A B C D}
        (f : ConPreorder.Con (Hom C D))
        (g : ConPreorder.Con (Hom B C))
        (h : ConPreorder.Con (Hom A B))
      → _≈CP_ (Hom A D) ((f ∘ g) ∘ h) (f ∘ (g ∘ h))

-- Optional strengthening: antisymmetry (partial orders) on all hom-preorders.

record Thin2CatPO {ℓObj ℓHom}
                 (C : Thin2Cat ℓObj ℓHom)
                 : Set (lsuc (ℓObj ⊔ ℓHom)) where
  open Thin2Cat C
  field
    poHom : ∀ {A B} → PartialOrder (Hom A B)

-- Antisymmetry upgrades the `≈`-level 2-category laws to definitional equality.

module Thin2CatLawsEq
  {ℓObj ℓHom}
  {C : Thin2Cat ℓObj ℓHom}
  (poC : Thin2CatPO C)
  (laws : Thin2CatLaws C)
  where

  open Thin2Cat C
  open Thin2CatPO poC
  open Thin2CatLaws laws

  id-left≡
    : ∀ {A B} (f : ConPreorder.Con (Hom A B))
    → (id ∘ f) ≡ f
  id-left≡ {A} {B} f = ≈CP→≡ (poHom {A = A} {B = B}) (id-left f)

  id-right≡
    : ∀ {A B} (f : ConPreorder.Con (Hom A B))
    → (f ∘ id) ≡ f
  id-right≡ {A} {B} f = ≈CP→≡ (poHom {A = A} {B = B}) (id-right f)

  assoc≡
    : ∀ {A B C' D}
      (f : ConPreorder.Con (Hom C' D))
      (g : ConPreorder.Con (Hom B C'))
      (h : ConPreorder.Con (Hom A B))
    → ((f ∘ g) ∘ h) ≡ (f ∘ (g ∘ h))
  assoc≡ {A} {D = D} f g h = ≈CP→≡ (poHom {A = A} {B = D}) (assoc f g h)

-- In a thin 2-category, 2-cells are preorder proofs. Horizontal composition
-- is just monotonicity in both arguments; vertical composition is `trans`.

comp-mono
  : ∀ {ℓObj ℓHom}
    {C : Thin2Cat ℓObj ℓHom}
    {A B C' : Thin2Cat.Obj C}
    {f f' : ConPreorder.Con (Thin2Cat.Hom C B C')}
    {g g' : ConPreorder.Con (Thin2Cat.Hom C A B)}
  → ConPreorder._⊑_ (Thin2Cat.Hom C B C') f f'
  → ConPreorder._⊑_ (Thin2Cat.Hom C A B) g g'
  → ConPreorder._⊑_ (Thin2Cat.Hom C A C') (Thin2Cat._∘_ C f g)
                                       (Thin2Cat._∘_ C f' g')
comp-mono {C = C} {A} {B} {C' = C'} {f = f} {f' = f'} f≤f' g≤g' =
  let
    step₁ = Thin2Cat.comp-mono-l C f≤f'
    step₂ = Thin2Cat.comp-mono-r C {f = f'} g≤g'
  in
  ConPreorder.trans (Thin2Cat.Hom C A C') step₁ step₂

-- Whiskering (2-cell transport) is immediate from monotonicity.

whisker-left
  : ∀ {ℓObj ℓHom}
    {C : Thin2Cat ℓObj ℓHom}
    {A B C' : Thin2Cat.Obj C}
    {f f' : ConPreorder.Con (Thin2Cat.Hom C B C')}
    {g : ConPreorder.Con (Thin2Cat.Hom C A B)}
  → ConPreorder._⊑_ (Thin2Cat.Hom C B C') f f'
  → ConPreorder._⊑_ (Thin2Cat.Hom C A C') (Thin2Cat._∘_ C f g)
                                       (Thin2Cat._∘_ C f' g)
whisker-left {C = C} = Thin2Cat.comp-mono-l C

whisker-right
  : ∀ {ℓObj ℓHom}
    {C : Thin2Cat ℓObj ℓHom}
    {A B C' : Thin2Cat.Obj C}
    {f : ConPreorder.Con (Thin2Cat.Hom C B C')}
    {g g' : ConPreorder.Con (Thin2Cat.Hom C A B)}
  → ConPreorder._⊑_ (Thin2Cat.Hom C A B) g g'
  → ConPreorder._⊑_ (Thin2Cat.Hom C A C') (Thin2Cat._∘_ C f g)
                                       (Thin2Cat._∘_ C f g')
whisker-right {C = C} = Thin2Cat.comp-mono-r C
