{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.LawSlice2Cat where

-- Common singleton law-slice packaging for optional ports.
--
-- This keeps the optional `*2Cat` modules on one local abstraction rather than
-- repeating direct imports of the low-level LT templates at each use site.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con)
open import LogOS.LT.Thin2Cat using (Thin2Cat)

import LogOS.LT.Ports.Template.LawSingleton2Cat as Template
import LogOS.LT.Ports.Template.Singleton2Cat as Singleton
import LogOS.LT.Ports.PortSig as PortSig

Singleton2Cat = Singleton.Singleton2Cat

lawPortSig = Template.lawPortSig

lawSlice2Cat = Template.lawSingleton2Cat

module Exports
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

  open Template.LawExports
    {C = C}
    {Tag = Tag}
    Unit
    Law
    idLaw
    compLaw
    public
