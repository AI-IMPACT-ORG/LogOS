{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Strict2Cat.PresentationH where

-- MetaTheory — Strict 2-category presentations (non-unique bases).
--
-- Presentation H: horizontal composition of 2-cells as primitive.

open import LogOS.Prelude
open import LogOS.LT.Thin2Cat using (Thin2Cat; Thin2CatLaws)

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using
  ( TwoCellOps
  ; TwoCellOpsLaws
  ; ≡→≈₂
  ; thinify₂
  ; thinify₂-laws
  )

record Strict2CatHOps (ℓObj ℓHom₁ ℓHom₂ : Level)
  : Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂)) where
  infixr 9 _∘1_
  infixr 5 _∙2_
  infixl 6 _⊗2_
  field
    Obj   : Set ℓObj
    Hom₁  : Obj → Obj → Set ℓHom₁
    Hom₂  : ∀ {A B} → Hom₁ A B → Hom₁ A B → Set ℓHom₂

    id1   : ∀ {A} → Hom₁ A A
    _∘1_  : ∀ {A B C₀} → Hom₁ B C₀ → Hom₁ A B → Hom₁ A C₀

    id2   : ∀ {A B} {f : Hom₁ A B} → Hom₂ f f
    _∙2_  : ∀ {A B} {f g h : Hom₁ A B} → Hom₂ f g → Hom₂ g h → Hom₂ f h

    -- Horizontal composition of 2-cells.
    _⊗2_
      : ∀ {A B C₀}
        {f f' : Hom₁ A B}
        {g g' : Hom₁ B C₀}
      → Hom₂ g g'
      → Hom₂ f f'
      → Hom₂ (g ∘1 f) (g' ∘1 f')

  -- Derived whiskering (so the TwoCellOps basis is always available).
  whiskerL2
    : ∀ {A B C₀} {g g' : Hom₁ B C₀} {f : Hom₁ A B}
    → Hom₂ g g'
    → Hom₂ (g ∘1 f) (g' ∘1 f)
  whiskerL2 {f = f} β = β ⊗2 (id2 {f = f})

  whiskerR2
    : ∀ {A B C₀} {g : Hom₁ B C₀} {f f' : Hom₁ A B}
    → Hom₂ f f'
    → Hom₂ (g ∘1 f) (g ∘1 f')
  whiskerR2 {g = g} α = (id2 {f = g}) ⊗2 α

record Strict2CatHLaws {ℓObj ℓHom₁ ℓHom₂ : Level} (C : Strict2CatHOps ℓObj ℓHom₁ ℓHom₂)
  : Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂)) where
  open Strict2CatHOps C using
    ( Hom₁
    ; Hom₂
    ; id1
    ; _∘1_
    ; id2
    ; _∙2_
    ; _⊗2_
    )
  field
    -- 1-cell laws (strict category on 1-cells).
    id1-left  : ∀ {A B} (f : Hom₁ A B) → (id1 {A = B}) ∘1 f ≡ f
    id1-right : ∀ {A B} (f : Hom₁ A B) → f ∘1 (id1 {A = A}) ≡ f
    assoc1
      : ∀ {A B C₀ D}
        (h : Hom₁ C₀ D)
        (g : Hom₁ B C₀)
        (f : Hom₁ A B)
      → (h ∘1 g) ∘1 f ≡ h ∘1 (g ∘1 f)

    -- 2-cell vertical laws (category on 2-cells in each hom).
    id2-left  : ∀ {A B} {f g : Hom₁ A B} (α : Hom₂ f g) → id2 ∙2 α ≡ α
    id2-right : ∀ {A B} {f g : Hom₁ A B} (α : Hom₂ f g) → α ∙2 id2 ≡ α
    assoc2
      : ∀ {A B} {f g h i : Hom₁ A B}
        (α : Hom₂ f g)
        (β : Hom₂ g h)
        (γ : Hom₂ h i)
      → (α ∙2 β) ∙2 γ ≡ α ∙2 (β ∙2 γ)

    -- Functoriality of horizontal composition (bifunctoriality).
    ⊗2-id
      : ∀ {A B C₀}
        {f : Hom₁ A B}
        {g : Hom₁ B C₀}
      → (id2 {f = g}) ⊗2 (id2 {f = f}) ≡ id2 {f = g ∘1 f}

    ⊗2-∙
      : ∀ {A B C₀}
        {f f' f'' : Hom₁ A B}
        {g g' g'' : Hom₁ B C₀}
        (β₁ : Hom₂ g g')
        (β₂ : Hom₂ g' g'')
        (α₁ : Hom₂ f f')
        (α₂ : Hom₂ f' f'')
      → (β₁ ∙2 β₂) ⊗2 (α₁ ∙2 α₂) ≡ (β₁ ⊗2 α₁) ∙2 (β₂ ⊗2 α₂)

record Strict2CatH (ℓObj ℓHom₁ ℓHom₂ : Level)
  : Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂)) where
  field
    ops : Strict2CatHOps ℓObj ℓHom₁ ℓHom₂
    laws : Strict2CatHLaws ops

Strict2CatH→TwoCellOps
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
  → Strict2CatH ℓObj ℓHom₁ ℓHom₂
  → TwoCellOps ℓObj ℓHom₁ ℓHom₂
Strict2CatH→TwoCellOps C =
  record
    { Obj = Obj
    ; Hom₁ = Hom₁
    ; Hom₂ = Hom₂
    ; id1 = id1
    ; _∘1_ = _∘1_
    ; id2 = id2
    ; _∙2_ = _∙2_
    ; whiskerL2 = whiskerL2
    ; whiskerR2 = whiskerR2
    }
  where
    open Strict2CatHOps (Strict2CatH.ops C) using
      ( Obj
      ; Hom₁
      ; Hom₂
      ; id1
      ; _∘1_
      ; id2
      ; _∙2_
      ; whiskerL2
      ; whiskerR2
      )

Strict2CatH→TwoCellOpsLaws
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
    (C : Strict2CatH ℓObj ℓHom₁ ℓHom₂)
  → TwoCellOpsLaws (Strict2CatH→TwoCellOps C)
Strict2CatH→TwoCellOpsLaws C =
  record
    { id-left = λ f → ≡→≈₂ {C = Derived} (Strict2CatHLaws.id1-left L f)
    ; id-right = λ f → ≡→≈₂ {C = Derived} (Strict2CatHLaws.id1-right L f)
    ; assoc = λ f g h → ≡→≈₂ {C = Derived} (Strict2CatHLaws.assoc1 L f g h)
    }
  where
    Ops = Strict2CatH.ops C
    L = Strict2CatH.laws C
    Derived = Strict2CatH→TwoCellOps C

    open Strict2CatHOps Ops using (Hom₂; id2; _∘1_)

Strict2CatH→Thin2Cat
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
  → Strict2CatH ℓObj ℓHom₁ ℓHom₂
  → Thin2Cat ℓObj ℓHom₁ ℓHom₂
Strict2CatH→Thin2Cat C = thinify₂ (Strict2CatH→TwoCellOps C)

Strict2CatH→Thin2CatLaws
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
    (C : Strict2CatH ℓObj ℓHom₁ ℓHom₂)
  → Thin2CatLaws (Strict2CatH→Thin2Cat C)
Strict2CatH→Thin2CatLaws C =
  thinify₂-laws (Strict2CatH→TwoCellOps C) (Strict2CatH→TwoCellOpsLaws C)

