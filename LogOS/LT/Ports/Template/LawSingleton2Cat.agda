{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Ports.Template.LawSingleton2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Port authoring template (law port, singleton case).
--
-- Many ports are “law ports”:
-- - the object payload is trivial (a chosen unit type to avoid `⊤` footguns),
-- - the displayed hom payload over a base morphism `f` is a law/proof `Law f`,
-- - identity and composition pick the canonical proofs (`idLaw`, `compLaw`),
-- - totalisation yields a thin 2-category with the same refinement as the base.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.DisplayedThin2Cat using (LawDisplayedOn)

import LogOS.LT.Ports.PortSig as PortSig
import LogOS.LT.Ports.Template.Singleton2Cat as Template

lawPortSig
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓTag ℓUnit ℓLaw : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Tag : Set ℓTag}
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
  → PortSig.PortSig C Tag
lawPortSig {ℓUnit = ℓUnit} {ℓLaw = ℓLaw} {C = C} Unit Law idLaw compLaw =
  record
    { ℓDObj = ℓUnit
    ; ℓDHom = ℓLaw
    ; Displayed = LawDisplayedOn C Unit Law idLaw compLaw
    }

lawSingleton2Cat
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓTag ℓUnit ℓLaw : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Tag : Set ℓTag}
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
  → Template.Singleton2Cat C Tag
lawSingleton2Cat Unit Law idLaw compLaw =
  Template.mkSingleton2Cat (lawPortSig Unit Law idLaw compLaw)

module LawExports
  {ℓObj ℓHomCon ℓHomRel ℓTag ℓUnit ℓLaw : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  {Tag : Set ℓTag}
  (Unit : Set ℓUnit)
  (Law : ∀ {A B} → Con (Thin2Cat.Hom C A B) → Set ℓLaw)
  (idLaw : ∀ {A} → Law (Thin2Cat.id C {A}))
  (compLaw
      : ∀ {A B C₀}
        {f : Con (Thin2Cat.Hom C A B)}
        {g : Con (Thin2Cat.Hom C B C₀)}
      → Law f
      → Law g
      → Law (Thin2Cat._∘_ C g f))
  where

  port2Cat : Template.Singleton2Cat C Tag
  port2Cat = lawSingleton2Cat Unit Law idLaw compLaw

  open Template.Singleton2Cat port2Cat public using
    ( singleton
    ; stack
    ; port
    ; Displayed
    ; WithPort
    ; forget
    )
