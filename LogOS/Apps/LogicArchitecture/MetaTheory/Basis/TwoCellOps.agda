{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps where

-- MetaTheory — A 2-Cell Basis (minimal interface + thinification).

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.Thin2Cat using (Thin2Cat; Thin2CatLaws)

-- ============================================================================
-- The 2-Cell Calculus (minimal interface)
-- ============================================================================

record TwoCellOps (ℓObj ℓHom₁ ℓHom₂ : Level)
  : Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂)) where
  infixr 9 _∘1_
  infixr 5 _∙2_
  field
    Obj   : Set ℓObj
    Hom₁  : Obj → Obj → Set ℓHom₁
    Hom₂  : ∀ {A B} → Hom₁ A B → Hom₁ A B → Set ℓHom₂

    id1   : ∀ {A} → Hom₁ A A
    _∘1_  : ∀ {A B C} → Hom₁ B C → Hom₁ A B → Hom₁ A C

    id2   : ∀ {A B} {f : Hom₁ A B} → Hom₂ f f
    _∙2_  : ∀ {A B} {f g h : Hom₁ A B} → Hom₂ f g → Hom₂ g h → Hom₂ f h

    whiskerL2
      : ∀ {A B C} {f f' : Hom₁ B C} {g : Hom₁ A B}
      → Hom₂ f f' → Hom₂ (f ∘1 g) (f' ∘1 g)

    whiskerR2
      : ∀ {A B C} {f : Hom₁ B C} {g g' : Hom₁ A B}
      → Hom₂ g g' → Hom₂ (f ∘1 g) (f ∘1 g')

-- ============================================================================
-- Thinification (local preorder shadow)
-- ============================================================================

HomPreorder
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
  → (C : TwoCellOps ℓObj ℓHom₁ ℓHom₂)
  → TwoCellOps.Obj C → TwoCellOps.Obj C
  → ConPreorder ℓHom₁ ℓHom₂
HomPreorder C A B =
  record
    { Con   = TwoCellOps.Hom₁ C A B
    ; _⊑_   = TwoCellOps.Hom₂ C
    ; refl  = TwoCellOps.id2 C
    ; trans = TwoCellOps._∙2_ C
    }

thinify₂
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
  → TwoCellOps ℓObj ℓHom₁ ℓHom₂
  → Thin2Cat ℓObj ℓHom₁ ℓHom₂
thinify₂ C =
  record
    { Obj = TwoCellOps.Obj C
    ; Hom = HomPreorder C
    ; id  = TwoCellOps.id1 C
    ; _∘_ = TwoCellOps._∘1_ C
    ; comp-mono-l = TwoCellOps.whiskerL2 C
    ; comp-mono-r = TwoCellOps.whiskerR2 C
    }

-- ============================================================================
-- Laws (up to mutual 2-cell)
-- ============================================================================

record TwoCellOpsLaws {ℓObj ℓHom₁ ℓHom₂}
  (C : TwoCellOps ℓObj ℓHom₁ ℓHom₂)
  : Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂)) where
  open TwoCellOps C using (Hom₁; Hom₂; id1; _∘1_)
  field
    id-left
      : ∀ {A B} (f : Hom₁ A B)
      → Hom₂ (id1 ∘1 f) f × Hom₂ f (id1 ∘1 f)

    id-right
      : ∀ {A B} (f : Hom₁ A B)
      → Hom₂ (f ∘1 id1) f × Hom₂ f (f ∘1 id1)

    assoc
      : ∀ {A B C D}
        (f : Hom₁ C D)
        (g : Hom₁ B C)
        (h : Hom₁ A B)
      → Hom₂ ((f ∘1 g) ∘1 h) (f ∘1 (g ∘1 h))
        × Hom₂ (f ∘1 (g ∘1 h)) ((f ∘1 g) ∘1 h)

thinify₂-laws
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
    (C : TwoCellOps ℓObj ℓHom₁ ℓHom₂)
  → TwoCellOpsLaws C
  → Thin2CatLaws (thinify₂ C)
thinify₂-laws _ L =
  record
    { id-left  = TwoCellOpsLaws.id-left L
    ; id-right = TwoCellOpsLaws.id-right L
    ; assoc    = TwoCellOpsLaws.assoc L
    }

-- --------------------------------------------------------------------------
-- Transport helpers: strict equalities as thin 2-cells.

-- Any strict equality of 1-cells yields a 2-cell (by transporting `id2`).
≡→Hom₂
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {A B : TwoCellOps.Obj C}
    {f g : TwoCellOps.Hom₁ C A B}
  → f ≡ g
  → TwoCellOps.Hom₂ C f g
≡→Hom₂ {C = C} refl = TwoCellOps.id2 C

-- Equality implies mutual 2-cell (the refinement-first stance: equalities only
-- *construct* 2-cells, laws live in G-tier).
≡→≈₂
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
    {C : TwoCellOps ℓObj ℓHom₁ ℓHom₂}
    {A B : TwoCellOps.Obj C}
    {f g : TwoCellOps.Hom₁ C A B}
  → f ≡ g
  → TwoCellOps.Hom₂ C f g × TwoCellOps.Hom₂ C g f
≡→≈₂ {C = C} eq =
  ( ≡→Hom₂ {C = C} eq
  , ≡→Hom₂ {C = C} (sym eq)
  )
