{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.CategoryTheory.WrapperCore where

-- Shared wrapper record cores for the CategoryTheory folder.
--
-- These are intentionally minimal: they do not add structure, they only package
-- existing refinement/≈ interfaces into reusable record shapes to avoid
-- boilerplate duplication across Kernel/Graded/LogicKernel variants.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)

-- A lightweight “refinement 2-category” interface:
-- 1-cells: morphisms
-- 2-cells: refinement (`_⇒_`) with whiskering and horizontal composition.

record Ref2Cat {ℓ : Level}
               (Sig : LogOSSignature ℓ)
               (Q : QAdapter ℓ)
               : Set (lsuc (lsuc (lsuc ℓ))) where
  infixr 9 _∘_
  infix  4 _⇒_
  infixr 7 _∙_
  infixr 6 _⊙_
  field
    Obj : Set (lsuc (lsuc ℓ))
    Hom : Obj → Obj → Set (lsuc (lsuc ℓ))
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    id  : ∀ {A} → Hom A A

    _⇒_ : ∀ {A B} → Hom A B → Hom A B → Set ℓ
    id⇒ : ∀ {A B} (f : Hom A B) → f ⇒ f
    _∙_ : ∀ {A B} {f g h : Hom A B} → f ⇒ g → g ⇒ h → f ⇒ h

    whiskerL : ∀ {A B C} (g : Hom B C) {f f' : Hom A B} → f ⇒ f' → (g ∘ f) ⇒ (g ∘ f')
    whiskerR : ∀ {A B C} {g g' : Hom B C} (f : Hom A B) → g ⇒ g' → (g ∘ f) ⇒ (g' ∘ f)
    _⊙_      : ∀ {A B C} {f f' : Hom A B} {g g' : Hom B C} → f ⇒ f' → g ⇒ g' → (g ∘ f) ⇒ (g' ∘ f')

-- A lightweight “Ho-category” interface:
-- quotient 1-cells by mutual refinement (≈), exposing ≈ as a setoid equality and
-- its congruence for composition.

record HoCat {ℓ : Level}
             (Sig : LogOSSignature ℓ)
             (Q : QAdapter ℓ)
             : Set (lsuc (lsuc (lsuc ℓ))) where
  infixr 9 _∘_
  infix  4 _≈_
  field
    Obj : Set (lsuc (lsuc ℓ))
    Hom : Obj → Obj → Set (lsuc (lsuc ℓ))
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    id  : ∀ {A} → Hom A A

    _≈_    : ∀ {A B} → Hom A B → Hom A B → Set ℓ
    refl≈  : ∀ {A B} (f : Hom A B) → f ≈ f
    sym≈   : ∀ {A B} {f g : Hom A B} → f ≈ g → g ≈ f
    trans≈ : ∀ {A B} {f g h : Hom A B} → f ≈ g → g ≈ h → f ≈ h

    cong-∘ : ∀ {A B C} {f f' : Hom A B} {g g' : Hom B C}
           → f ≈ f' → g ≈ g' → (g ∘ f) ≈ (g' ∘ f')

