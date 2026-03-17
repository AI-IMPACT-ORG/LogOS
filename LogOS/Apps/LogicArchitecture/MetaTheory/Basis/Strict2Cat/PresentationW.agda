{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Strict2Cat.PresentationW where

-- MetaTheory — Strict 2-category presentations (non-unique bases).
--
-- Presentation W: whiskering + middle-four interchange as primitive.

open import LogOS.Prelude
open import LogOS.LT.Thin2Cat using (Thin2Cat; Thin2CatLaws)

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using
  ( TwoCellOps
  ; TwoCellOpsLaws
  ; ≡→≈₂
  ; thinify₂
  ; thinify₂-laws
  )

record Strict2CatWLaws {ℓObj ℓHom₁ ℓHom₂ : Level} (C : TwoCellOps ℓObj ℓHom₁ ℓHom₂)
  : Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂)) where
  open TwoCellOps C using
    ( Hom₁
    ; Hom₂
    ; id1
    ; _∘1_
    ; id2
    ; _∙2_
    ; whiskerL2
    ; whiskerR2
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

    -- Middle-four interchange: the two canonical pastings coincide.
    middle4
      : ∀ {A B C₀}
        {f f' : Hom₁ A B}
        {g g' : Hom₁ B C₀}
        (α : Hom₂ f f')
        (β : Hom₂ g g')
      → (whiskerR2 {f = g} α ∙2 whiskerL2 {g = f'} β)
        ≡
        (whiskerL2 {g = f} β ∙2 whiskerR2 {f = g'} α)

record Strict2CatW (ℓObj ℓHom₁ ℓHom₂ : Level)
  : Set (lsuc (ℓObj ⊔ ℓHom₁ ⊔ ℓHom₂)) where
  field
    ops : TwoCellOps ℓObj ℓHom₁ ℓHom₂
    laws : Strict2CatWLaws ops

Strict2CatW→TwoCellOps
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
  → Strict2CatW ℓObj ℓHom₁ ℓHom₂
  → TwoCellOps ℓObj ℓHom₁ ℓHom₂
Strict2CatW→TwoCellOps = Strict2CatW.ops

Strict2CatW→TwoCellOpsLaws
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
    (C : Strict2CatW ℓObj ℓHom₁ ℓHom₂)
  → TwoCellOpsLaws (Strict2CatW→TwoCellOps C)
Strict2CatW→TwoCellOpsLaws C =
  let
    Ops = Strict2CatW.ops C
    L = Strict2CatW.laws C
  in
  let open TwoCellOps Ops in
  record
    { id-left = λ f → ≡→≈₂ {C = Ops} (Strict2CatWLaws.id1-left L f)
    ; id-right = λ f → ≡→≈₂ {C = Ops} (Strict2CatWLaws.id1-right L f)
    ; assoc = λ f g h → ≡→≈₂ {C = Ops} (Strict2CatWLaws.assoc1 L f g h)
    }

Strict2CatW→Thin2Cat
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
  → Strict2CatW ℓObj ℓHom₁ ℓHom₂
  → Thin2Cat ℓObj ℓHom₁ ℓHom₂
Strict2CatW→Thin2Cat C = thinify₂ (Strict2CatW.ops C)

Strict2CatW→Thin2CatLaws
  : ∀ {ℓObj ℓHom₁ ℓHom₂}
    (C : Strict2CatW ℓObj ℓHom₁ ℓHom₂)
  → Thin2CatLaws (Strict2CatW→Thin2Cat C)
Strict2CatW→Thin2CatLaws C =
  thinify₂-laws (Strict2CatW.ops C) (Strict2CatW→TwoCellOpsLaws C)

