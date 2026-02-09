{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.CategoryTheory.WrapperCore where

-- Shared wrapper record cores for the CategoryTheory folder.
--
-- These are intentionally minimal: they do not add structure, they only package
-- existing refinement/≈ interfaces into reusable record shapes to avoid
-- boilerplate duplication across Kernel/Graded variants.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder)
open import LogOS.Minimal.Thin2Cat as Thin2Cat using (Thin2Cat)
open import LogOS.Minimal.RelPreorder as RP using (RelPreorder)
open import LogOS.Minimal.RelThin2Cat as RelThin2Cat using (RelThin2Cat)

-- A lightweight “refinement 2-category” interface (laws not bundled):
-- 1-cells: morphisms
-- 2-cells: refinement (`_⇒_`) with whiskering and horizontal composition.

record Ref2CatCore (ℓObj ℓHom ℓ₂ : Level) : Set (lsuc (ℓObj ⊔ ℓHom ⊔ ℓ₂)) where
  infixr 9 _∘_
  infix  4 _⇒_
  infixr 7 _∙_
  infixr 6 _⊙_
  field
    Obj : Set ℓObj
    Hom : Obj → Obj → Set ℓHom
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    id  : ∀ {A} → Hom A A

    _⇒_ : ∀ {A B} → Hom A B → Hom A B → Set ℓ₂
    id⇒ : ∀ {A B} (f : Hom A B) → f ⇒ f
    _∙_ : ∀ {A B} {f g h : Hom A B} → f ⇒ g → g ⇒ h → f ⇒ h

    whiskerL : ∀ {A B C} (g : Hom B C) {f f' : Hom A B} → f ⇒ f' → (g ∘ f) ⇒ (g ∘ f')
    whiskerR : ∀ {A B C} {g g' : Hom B C} (f : Hom A B) → g ⇒ g' → (g ∘ f) ⇒ (g' ∘ f)
    _⊙_      : ∀ {A B C} {f f' : Hom A B} {g g' : Hom B C} → f ⇒ f' → g ⇒ g' → (g ∘ f) ⇒ (g' ∘ f')

-- Signature-aligned alias (kept for kernel-facing interfaces).
-- Specialization for kernel-level universes (Sig/Q only fix levels).
Ref2Cat
  : ∀ {ℓ : Level}
    (Sig : LogOSSignature ℓ)
    (Q : QAdapter ℓ)
  → Set (lsuc (lsuc (lsuc ℓ)))
Ref2Cat {ℓ} _ _ = Ref2CatCore (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ)) ℓ

-- A lightweight “Ho-category” interface:
-- quotient 1-cells by mutual refinement (≈), exposing ≈ as a setoid equality and
-- its congruence for composition.

record HoCatCore (ℓObj ℓHom ℓEq : Level) : Set (lsuc (ℓObj ⊔ ℓHom ⊔ ℓEq)) where
  infixr 9 _∘_
  infix  4 _⇒_
  infixr 6 _⊙_
  field
    Obj : Set ℓObj
    Hom : Obj → Obj → Set ℓHom
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    id  : ∀ {A} → Hom A A

    -- Primitive notion: refinement (a preorder on each hom-set).
    _⇒_     : ∀ {A B} → Hom A B → Hom A B → Set ℓEq
    refl⇒   : ∀ {A B} (f : Hom A B) → f ⇒ f
    trans⇒  : ∀ {A B} {f g h : Hom A B} → f ⇒ g → g ⇒ h → f ⇒ h

    -- Composition monotonicity (enough to derive Ho-category congruence).
    whiskerL : ∀ {A B C} (g : Hom B C) {f f' : Hom A B} → f ⇒ f' → (g ∘ f) ⇒ (g ∘ f')
    whiskerR : ∀ {A B C} {g g' : Hom B C} (f : Hom A B) → g ⇒ g' → (g ∘ f) ⇒ (g' ∘ f)
    _⊙_      : ∀ {A B C} {f f' : Hom A B} {g g' : Hom B C} → f ⇒ f' → g ⇒ g' → (g ∘ f) ⇒ (g' ∘ f')

  -- Derived: mutual refinement (Ho-category equality).
  infix 4 _≈_
  _≈_ : ∀ {A B} → Hom A B → Hom A B → Set ℓEq
  f ≈ g = (f ⇒ g) × (g ⇒ f)

  refl≈ : ∀ {A B} (f : Hom A B) → f ≈ f
  refl≈ f = refl⇒ f , refl⇒ f

  sym≈ : ∀ {A B} {f g : Hom A B} → f ≈ g → g ≈ f
  sym≈ (fg , gf) = gf , fg

  trans≈ : ∀ {A B} {f g h : Hom A B} → f ≈ g → g ≈ h → f ≈ h
  trans≈ {f = f} {g = g} {h = h} (fg , gf) (gh , hg) =
    trans⇒ {f = f} {g = g} {h = h} fg gh
    ,
    trans⇒ {f = h} {g = g} {h = f} hg gf

  -- Composition respects ≈ (Ho-category congruence).
  cong-∘ : ∀ {A B C} {f f' : Hom A B} {g g' : Hom B C}
         → f ≈ f' → g ≈ g' → (g ∘ f) ≈ (g' ∘ f')
  cong-∘ {f = f} {f' = f'} {g = g} {g' = g'} (ff' , f'f) (gg' , g'g) =
    (_⊙_ {f = f} {f' = f'} {g = g} {g' = g'} ff' gg')
    ,
    (_⊙_ {f = f'} {f' = f} {g = g'} {g' = g} f'f g'g)

-- Specialization for kernel-level universes (Sig/Q only fix levels).
HoCat
  : ∀ {ℓ : Level}
    (Sig : LogOSSignature ℓ)
    (Q : QAdapter ℓ)
  → Set (lsuc (lsuc (lsuc ℓ)))
HoCat {ℓ} _ _ = HoCatCore (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ)) ℓ

-- --------------------------------------------------------------------------
-- Generic conversion: any Thin2Cat yields a Ref2CatCore where 2-cells are the
-- hom-preorder relation `_⊑_`.
--
-- This is a pure wrapper: no additional axioms are introduced.
-- --------------------------------------------------------------------------

Thin2Cat→Ref2CatCore
  : ∀ {ℓObj ℓHom}
  → Thin2Cat ℓObj ℓHom
  → Ref2CatCore ℓObj ℓHom ℓHom
Thin2Cat→Ref2CatCore C =
  record
    { Obj = Thin2Cat.Obj C
    ; Hom = λ A B → ConPreorder.Con (Thin2Cat.Hom C A B)
    ; _∘_ = Thin2Cat._∘_ C
    ; id  = Thin2Cat.id C
    ; _⇒_ = λ {A} {B} f g → ConPreorder._⊑_ (Thin2Cat.Hom C A B) f g
    ; id⇒ = λ {A} {B} f → ConPreorder.refl (Thin2Cat.Hom C A B)
    ; _∙_ = λ {A} {B} {f} {g} {h} fg gh →
        ConPreorder.trans (Thin2Cat.Hom C A B) fg gh
    ; whiskerL = λ {A} {B} {C'} g {f} {f'} ff' →
        Thin2Cat.comp-mono-r C {f = g} {g = f} {g' = f'} ff'
    ; whiskerR = λ {A} {B} {C'} {g} {g'} f gg' →
        Thin2Cat.comp-mono-l C {f = g} {f' = g'} {g = f} gg'
    ; _⊙_ = λ {A} {B} {C'} {f} {f'} {g} {g'} ff' gg' →
        let
          step₁ =
            Thin2Cat.comp-mono-r C {f = g} {g = f} {g' = f'} ff'
          step₂ =
            Thin2Cat.comp-mono-l C {f = g} {f' = g'} {g = f'} gg'
        in
        ConPreorder.trans (Thin2Cat.Hom C A C') step₁ step₂
    }

-- Generic conversion: any RelThin2Cat yields a Ref2CatCore where 2-cells are the
-- hom-relation `_⊑_` (no same-universe constraint needed).

RelThin2Cat→Ref2CatCore
  : ∀ {ℓObj ℓHom ℓ₂}
  → RelThin2Cat ℓObj ℓHom ℓ₂
  → Ref2CatCore ℓObj ℓHom ℓ₂
RelThin2Cat→Ref2CatCore C =
  record
    { Obj = RelThin2Cat.Obj C
    ; Hom = λ A B → RelPreorder.Con (RelThin2Cat.Hom C A B)
    ; _∘_ = RelThin2Cat._∘_ C
    ; id  = RelThin2Cat.id C
    ; _⇒_ = λ {A} {B} f g → RelPreorder._⊑_ (RelThin2Cat.Hom C A B) f g
    ; id⇒ = λ {A} {B} f → RelPreorder.refl (RelThin2Cat.Hom C A B)
    ; _∙_ = λ {A} {B} {f} {g} {h} fg gh →
        RelPreorder.trans (RelThin2Cat.Hom C A B) fg gh
    ; whiskerL = λ {A} {B} {C'} g {f} {f'} ff' →
        RelThin2Cat.comp-mono-r C {f = g} {g = f} {g' = f'} ff'
    ; whiskerR = λ {A} {B} {C'} {g} {g'} f gg' →
        RelThin2Cat.comp-mono-l C {f = g} {f' = g'} {g = f} gg'
    ; _⊙_ = λ {A} {B} {C'} {f} {f'} {g} {g'} ff' gg' →
        let
          step₁ =
            RelThin2Cat.comp-mono-r C {f = g} {g = f} {g' = f'} ff'
          step₂ =
            RelThin2Cat.comp-mono-l C {f = g} {f' = g'} {g = f'} gg'
        in
        RelPreorder.trans (RelThin2Cat.Hom C A C') step₁ step₂
    }
