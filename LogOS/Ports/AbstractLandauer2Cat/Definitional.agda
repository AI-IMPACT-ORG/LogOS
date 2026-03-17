{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.AbstractLandauer2Cat.Definitional where

open import LogOS.Prelude using (Level; _≡_)
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.DisplayedThin2Cat using
  ( DecoratedThin2Cat
  ; forgetDecorated
  )
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (JoinPrequantale)
open import LogOS.Ports.AbstractLandauer.Ledger using (LandauerAssumptions)

import LogOS.Ports.AbstractLandauer2Cat as Landauer2Cat
import LogOS.LT.Ports.Template.Singleton2CatDefinitional as SingletonDef

WithLandauer-def
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
    (L : LandauerAssumptions C Scale JP)
  → Landauer2Cat.WithPort {C = C} L
    ≡
    DecoratedThin2Cat (Landauer2Cat.Displayed {C = C} L)
WithLandauer-def L = SingletonDef.withPort≡ (Landauer2Cat.port2Cat L)

forgetLandauer-def
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓScaleCon ℓScaleRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {Scale : ConPreorder ℓScaleCon ℓScaleRel}
    {JP : JoinPrequantale Scale}
    (L : LandauerAssumptions C Scale JP)
  → Landauer2Cat.forget {C = C} L
    ≡
    forgetDecorated (Landauer2Cat.Displayed {C = C} L)
forgetLandauer-def L = SingletonDef.forget≡ (Landauer2Cat.port2Cat L)
