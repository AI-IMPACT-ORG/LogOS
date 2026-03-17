{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.PseudoFunctor where

-- MetaTheory — Pseudofunctor-shaped presentations (as additional law bundles).
--
-- LogOS alignment:
-- - the *operations* basis is `TwoCellOps`,
-- - “functoriality up to 2-cell” is an explicit record over that basis,
-- - full pseudofunctor coherence (various equivalent axiomatisations) is a
--   separate optional law bundle.
--
-- The key point for the LT architecture is: any such presentation induces a
-- canonical `Thin2Functor` between thinifications.

open import LogOS.Prelude
open import LogOS.LT.Thin2Functor using (Thin2Functor)

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using
  ( TwoCellOps
  ; thinify₂
  )

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Bicategory using
  ( BicatW
  ; BicatW→TwoCellOps
  ; BicatW→Thin2Cat
  )

-- ============================================================================
-- Basis-level: “functor up to 2-cell” between TwoCellOps presentations
-- ============================================================================

record TwoCellOpsFunctor
  {ℓObj₁ ℓHom₁₁ ℓHom₂₁ ℓObj₂ ℓHom₁₂ ℓHom₂₂ : Level}
  (C₁ : TwoCellOps ℓObj₁ ℓHom₁₁ ℓHom₂₁)
  (C₂ : TwoCellOps ℓObj₂ ℓHom₁₂ ℓHom₂₂)
  : Set (lsuc (ℓObj₁ ⊔ ℓHom₁₁ ⊔ ℓHom₂₁ ⊔ ℓObj₂ ⊔ ℓHom₁₂ ⊔ ℓHom₂₂)) where
  private
    module C₁ = TwoCellOps C₁
    module C₂ = TwoCellOps C₂
  field
    mapObj : C₁.Obj → C₂.Obj

    mapHom₁
      : ∀ {A B}
      → C₁.Hom₁ A B
      → C₂.Hom₁ (mapObj A) (mapObj B)

    mapHom₂
      : ∀ {A B} {f g : C₁.Hom₁ A B}
      → C₁.Hom₂ f g
      → C₂.Hom₂ (mapHom₁ f) (mapHom₁ g)

    -- Identity and composition preserved up to mutual 2-cell.
    id1-pres₂
      : ∀ {A}
      → C₂.Hom₂ (mapHom₁ (C₁.id1 {A = A})) (C₂.id1 {A = mapObj A})

    id1-pres₂⁻
      : ∀ {A}
      → C₂.Hom₂ (C₂.id1 {A = mapObj A}) (mapHom₁ (C₁.id1 {A = A}))

    comp-pres₂
      : ∀ {A B C}
        (f : C₁.Hom₁ B C)
        (g : C₁.Hom₁ A B)
      → C₂.Hom₂ (mapHom₁ (f C₁.∘1 g)) (mapHom₁ f C₂.∘1 mapHom₁ g)

    comp-pres₂⁻
      : ∀ {A B C}
        (f : C₁.Hom₁ B C)
        (g : C₁.Hom₁ A B)
      → C₂.Hom₂ (mapHom₁ f C₂.∘1 mapHom₁ g) (mapHom₁ (f C₁.∘1 g))

TwoCellOpsFunctor→Thin2Functor
  : ∀ {ℓObj₁ ℓHom₁₁ ℓHom₂₁ ℓObj₂ ℓHom₁₂ ℓHom₂₂}
    {C₁ : TwoCellOps ℓObj₁ ℓHom₁₁ ℓHom₂₁}
    {C₂ : TwoCellOps ℓObj₂ ℓHom₁₂ ℓHom₂₂}
  → TwoCellOpsFunctor C₁ C₂
  → Thin2Functor (thinify₂ C₁) (thinify₂ C₂)
TwoCellOpsFunctor→Thin2Functor {C₁ = C₁} {C₂ = C₂} F =
  let
    module C₁ = TwoCellOps C₁
    module C₂ = TwoCellOps C₂
  in
  record
    { mapObj = TwoCellOpsFunctor.mapObj F
    ; mapHom = λ f → TwoCellOpsFunctor.mapHom₁ F f
    ; mapHom-mono =
        λ {A} {B} {x} {y} le →
          TwoCellOpsFunctor.mapHom₂ F le
    ; id-pres = λ {A} →
        ( TwoCellOpsFunctor.id1-pres₂ F {A = A}
        , TwoCellOpsFunctor.id1-pres₂⁻ F {A = A}
        )
    ; comp-pres =
        λ {A} {B} {C} f g →
          ( TwoCellOpsFunctor.comp-pres₂ F f g
          , TwoCellOpsFunctor.comp-pres₂⁻ F f g
          )
    }

-- ============================================================================
-- Bicategory-level surface (same underlying ops-functor, optional extra laws)
-- ============================================================================

PseudoFunctor
  : ∀ {ℓObj₁ ℓHom₁₁ ℓHom₂₁ ℓObj₂ ℓHom₁₂ ℓHom₂₂}
  → BicatW ℓObj₁ ℓHom₁₁ ℓHom₂₁
  → BicatW ℓObj₂ ℓHom₁₂ ℓHom₂₂
  → Set (lsuc (ℓObj₁ ⊔ ℓHom₁₁ ⊔ ℓHom₂₁ ⊔ ℓObj₂ ⊔ ℓHom₁₂ ⊔ ℓHom₂₂))
PseudoFunctor B₁ B₂ =
  TwoCellOpsFunctor (BicatW→TwoCellOps B₁) (BicatW→TwoCellOps B₂)

PseudoFunctor→Thin2Functor
  : ∀ {ℓObj₁ ℓHom₁₁ ℓHom₂₁ ℓObj₂ ℓHom₁₂ ℓHom₂₂}
    {B₁ : BicatW ℓObj₁ ℓHom₁₁ ℓHom₂₁}
    {B₂ : BicatW ℓObj₂ ℓHom₁₂ ℓHom₂₂}
  → PseudoFunctor B₁ B₂
  → Thin2Functor (BicatW→Thin2Cat B₁) (BicatW→Thin2Cat B₂)
PseudoFunctor→Thin2Functor = TwoCellOpsFunctor→Thin2Functor

-- Optional: full pseudofunctor coherence (several equivalent formulations).
--
-- If you want this to be “manifestly literature-grade”, we should choose:
-- - an orientation for the compositor/unitor constraints (ours are `F(f∘g) → Ff∘Fg`),
-- - a coherence axiomatisation (e.g. Street vs Leinster style).
-- Both choices are equivalent up to systematic inversion, but not syntactically.
record PseudoFunctorCoherence
  {ℓObj₁ ℓHom₁₁ ℓHom₂₁ ℓObj₂ ℓHom₁₂ ℓHom₂₂ : Level}
  {B₁ : BicatW ℓObj₁ ℓHom₁₁ ℓHom₂₁}
  {B₂ : BicatW ℓObj₂ ℓHom₁₂ ℓHom₂₂}
  (F : PseudoFunctor B₁ B₂)
  : Set (lsuc (ℓObj₁ ⊔ ℓHom₁₁ ⊔ ℓHom₂₁ ⊔ ℓObj₂ ⊔ ℓHom₁₂ ⊔ ℓHom₂₂)) where
  -- Placeholder: add the standard coherence equalities here once a concrete
  -- axiomatisation is selected.
