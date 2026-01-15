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
  infix  4 _≈_
  field
    Obj : Set ℓObj
    Hom : Obj → Obj → Set ℓHom
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    id  : ∀ {A} → Hom A A

    _≈_    : ∀ {A B} → Hom A B → Hom A B → Set ℓEq
    refl≈  : ∀ {A B} (f : Hom A B) → f ≈ f
    sym≈   : ∀ {A B} {f g : Hom A B} → f ≈ g → g ≈ f
    trans≈ : ∀ {A B} {f g h : Hom A B} → f ≈ g → g ≈ h → f ≈ h

    cong-∘ : ∀ {A B C} {f f' : Hom A B} {g g' : Hom B C}
           → f ≈ f' → g ≈ g' → (g ∘ f) ≈ (g' ∘ f')

-- Specialization for kernel-level universes (Sig/Q only fix levels).
HoCat
  : ∀ {ℓ : Level}
    (Sig : LogOSSignature ℓ)
    (Q : QAdapter ℓ)
  → Set (lsuc (lsuc (lsuc ℓ)))
HoCat {ℓ} _ _ = HoCatCore (lsuc (lsuc ℓ)) (lsuc (lsuc ℓ)) ℓ
