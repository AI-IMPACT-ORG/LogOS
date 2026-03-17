{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Thin2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; _⊑_; _≈_; refl⊑)

-- Locally preordered 2-category interface (2-cells are refinement witnesses).
--
-- In the literature this is a *locally preordered 2-category* (equivalently:
-- a category enriched in preorders).
--
-- In v1.1, “2-cells” are refinement proofs `f ⊑ g` in the hom-preorders, so
-- there may be multiple inhabitants of the same refinement type (proof-relevant
-- formulation by default).
-- If hom-preorders are proof-irrelevant, there is at most one proof of
-- `f ⊑ g` (so at most one 2-cell between fixed 1-cells). Antisymmetry is a
-- separate strengthening: it collapses `≈` to propositional equality of
-- 1-cells, not proof-irrelevance of refinement proofs.
--
-- Laws are stated up to mutual refinement (`≈`), not as strict propositional equalities (`≡`).

record Thin2Cat (ℓObj ℓHomCon ℓHomRel : Level)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  infixr 9 _∘_
  field
    Obj : Set ℓObj
    Hom : Obj → Obj → ConPreorder ℓHomCon ℓHomRel

    id  : ∀ {A} → Con (Hom A A)
    _∘_ : ∀ {A B C} → Con (Hom B C) → Con (Hom A B) → Con (Hom A C)

    comp-mono-l
      : ∀ {A B C} {f f' : Con (Hom B C)} {g : Con (Hom A B)}
      → _⊑_ (Hom B C) f f'
      → _⊑_ (Hom A C) (f ∘ g) (f' ∘ g)

    comp-mono-r
      : ∀ {A B C} {f : Con (Hom B C)} {g g' : Con (Hom A B)}
      → _⊑_ (Hom A B) g g'
      → _⊑_ (Hom A C) (f ∘ g) (f ∘ g')

-- --------------------------------------------------------------------------
-- Reindexing: pull back a thin 2-category along an object map.
--
-- Given an object map `F : Obj' → Obj C`, this constructs the thin 2-category
-- whose:
-- - objects are `Obj'`, and
-- - hom-preorders are inherited from `C` by reindexing along `F`.
--
-- This is the categorified version of “pullback a relation along a map”.
PullbackThin2Cat
  : ∀ {ℓObj' ℓObj ℓHomCon ℓHomRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → (Obj' : Set ℓObj')
  → (F : Obj' → Thin2Cat.Obj C)
  → Thin2Cat ℓObj' ℓHomCon ℓHomRel
PullbackThin2Cat {C = C} Obj' F =
  let module C = Thin2Cat C in
  record
    { Obj = Obj'
    ; Hom = λ A B → C.Hom (F A) (F B)
    ; id = λ {A} → C.id {A = F A}
    ; _∘_ = λ {A} {B} {C₀} f g → f C.∘ g
    ; comp-mono-l = λ {A} {B} {C₀} {f} {f'} {g} le → C.comp-mono-l le
    ; comp-mono-r = λ {A} {B} {C₀} {f} {g} {g'} le → C.comp-mono-r le
    }

record Thin2CatLaws {ℓObj ℓHomCon ℓHomRel} (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel)) where
  open Thin2Cat C
  field
    id-left  : ∀ {A B} (f : Con (Hom A B)) → _≈_ (Hom A B) (id ∘ f) f
    id-right : ∀ {A B} (f : Con (Hom A B)) → _≈_ (Hom A B) (f ∘ id) f
    assoc
      : ∀ {A B C D}
        (f : Con (Hom C D))
        (g : Con (Hom B C))
        (h : Con (Hom A B))
      → _≈_ (Hom A D) ((f ∘ g) ∘ h) (f ∘ (g ∘ h))

-- Convenient “2-cell” vocabulary (derived, no extra structure):
-- refinement proofs in the hom-preorders, with vertical composition = transitivity.
module Thin2Cat₂Cells {ℓObj ℓHomCon ℓHomRel} (C : Thin2Cat ℓObj ℓHomCon ℓHomRel) where
  open Thin2Cat C
  infix 4 _⇒_
  _⇒_ : ∀ {A B} → Con (Hom A B) → Con (Hom A B) → Set ℓHomRel
  _⇒_ {A} {B} f g = _⊑_ (Hom A B) f g

  id₂ : ∀ {A B} {f : Con (Hom A B)} → f ⇒ f
  id₂ {A} {B} {f} = refl⊑ (Hom A B)

  infixr 5 _∙_
  _∙_ : ∀ {A B} {f g h : Con (Hom A B)} → f ⇒ g → g ⇒ h → f ⇒ h
  _∙_ {A} {B} {f} {g} {h} fg gh =
    let
      module R = LogOS.Prelude.RefinementKit.Reasoning (Hom A B)
    in
    R._⊑⟨_⟩_ f fg gh

  whiskerL
    : ∀ {A B C'} {f f' : Con (Hom B C')} {g : Con (Hom A B)}
    → f ⇒ f'
    → (f ∘ g) ⇒ (f' ∘ g)
  whiskerL = comp-mono-l

  whiskerR
    : ∀ {A B C'} {f : Con (Hom B C')} {g g' : Con (Hom A B)}
    → g ⇒ g'
    → (f ∘ g) ⇒ (f ∘ g')
  whiskerR = comp-mono-r

-- Further thin-2-categorical constructions are factored into submodules:
-- - `LogOS.LT.Thin2Cat.WeakTerminal`
-- - `LogOS.LT.Thin2Cat.Endo`
