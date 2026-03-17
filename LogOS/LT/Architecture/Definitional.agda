{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Architecture.Definitional where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Equality quarantine for architecture constructor bookkeeping.
--
-- These witnesses are intentionally kept off the default LT/API surfaces. They
-- exist only for explicit definitional checks and documentation.

open import LogOS.Prelude
open import LogOS.LT.Thin2Cat using (Thin2Cat; PullbackThin2Cat)
open import LogOS.LT.Thin2Functor using (forgetPullbackThin2Functor)
open import LogOS.LT.DisplayedThin2Cat using
  ( DisplayedThin2Cat
  ; DecoratedThin2Cat
  ; forgetDecorated
  )
open import LogOS.LT.Architecture.Apex using
  ( Apex
  ; forget
  ; pullbackApexOver
  ; displayedApexOver
  )

Apex-pullbackApexOver≡
  : ∀ {ℓObj' ℓObj ℓHomCon ℓHomRel : Level}
    {E : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (Obj' : Set ℓObj')
    (F : Obj' → Thin2Cat.Obj E)
  → Apex (pullbackApexOver {E = E} Obj' F) ≡ PullbackThin2Cat {C = E} Obj' F
Apex-pullbackApexOver≡ _ _ = refl

forget-pullbackApexOver≡
  : ∀ {ℓObj' ℓObj ℓHomCon ℓHomRel : Level}
    {E : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (Obj' : Set ℓObj')
    (F : Obj' → Thin2Cat.Obj E)
  → forget (pullbackApexOver {E = E} Obj' F)
      ≡ forgetPullbackThin2Functor {C = E} Obj' F
forget-pullbackApexOver≡ _ _ = refl

Apex-displayedApexOver≡
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom : Level}
    {E : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (D : DisplayedThin2Cat E ℓDObj ℓDHom)
  → Apex (displayedApexOver D) ≡ DecoratedThin2Cat D
Apex-displayedApexOver≡ _ = refl

forget-displayedApexOver≡
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom : Level}
    {E : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (D : DisplayedThin2Cat E ℓDObj ℓDHom)
  → forget (displayedApexOver D) ≡ forgetDecorated D
forget-displayedApexOver≡ _ = refl
