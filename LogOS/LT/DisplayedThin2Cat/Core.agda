{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.DisplayedThin2Cat.Core where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Displayed thin 2-categories (data-only; obligations on 1-cells).
--
-- This module is a pure “displayed data” layer: it introduces a displayed
-- structure over a base `Thin2Cat`, but deliberately does *not* expose any
-- cleavage/fibration interface.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con)
open import LogOS.LT.Thin2Cat using (Thin2Cat)

record DisplayedThin2Cat
  {ℓObj ℓHomCon ℓHomRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  (ℓDObj ℓDHom : Level)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel ⊔ ℓDObj ⊔ ℓDHom)) where
  private module B = Thin2Cat C
  field
    Ob
      : B.Obj → Set ℓDObj

    HomD
      : ∀ {A B}
      → (f : Con (B.Hom A B))
      → Ob A → Ob B → Set ℓDHom

    idD
      : ∀ {A} (x : Ob A)
      → HomD (B.id {A}) x x

    compD
      : ∀ {A B C₀}
        {f : Con (B.Hom A B)}
        {g : Con (B.Hom B C₀)}
        {x : Ob A} {y : Ob B} {z : Ob C₀}
      → HomD f x y
      → HomD g y z
      → HomD (g B.∘ f) x z

open DisplayedThin2Cat public using (Ob; HomD; idD; compD)

-- --------------------------------------------------------------------------
-- Law ports: displayed layers with no object payload (Ob = ⊤).

LawDisplayed
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓLaw : Level}
    (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  → (Law : ∀ {A B} → Con (Thin2Cat.Hom C A B) → Set ℓLaw)
  → (idLaw : ∀ {A} → Law (Thin2Cat.id C {A}))
  → (compLaw
      : ∀ {A B C₀}
        {f : Con (Thin2Cat.Hom C A B)}
        {g : Con (Thin2Cat.Hom C B C₀)}
      → Law f
      → Law g
      → Law (Thin2Cat._∘_ C g f))
  → DisplayedThin2Cat C lzero ℓLaw
LawDisplayed C Law idLaw compLaw =
  let module B = Thin2Cat C in
  record
    { Ob = λ _ → ⊤ {lzero}
    ; HomD = λ {A} {B₀} (f : Con (B.Hom A B₀)) _ _ → Law f
    ; idD = λ _ → idLaw
    ; compD = λ lf lg → compLaw lf lg
    }

-- Variant: allow choosing the unit type used for “no object payload”.
LawDisplayedOn
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓUnit ℓLaw : Level}
    (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  → (Unit : Set ℓUnit)
  → (Law : ∀ {A B} → Con (Thin2Cat.Hom C A B) → Set ℓLaw)
  → (idLaw : ∀ {A} → Law (Thin2Cat.id C {A}))
  → (compLaw
      : ∀ {A B C₀}
        {f : Con (Thin2Cat.Hom C A B)}
        {g : Con (Thin2Cat.Hom C B C₀)}
      → Law f
      → Law g
      → Law (Thin2Cat._∘_ C g f))
  → DisplayedThin2Cat C ℓUnit ℓLaw
LawDisplayedOn C Unit Law idLaw compLaw =
  let module B = Thin2Cat C in
  record
    { Ob = λ _ → Unit
    ; HomD = λ {A} {B₀} (f : Con (B.Hom A B₀)) _ _ → Law f
    ; idD = λ _ → idLaw
    ; compD = λ lf lg → compLaw lf lg
    }

