{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.AbstractLandauerStack2Cat where

-- Generic Landauer law-port stack over an arbitrary thin 2-category.
--
-- This factors out the recurring pattern:
-- - fix a base thin 2-category `C`,
-- - choose a quantitative adapter `Q`,
-- - attach the Landauer cost law-port as a singleton stack,
-- - expose the standard displayed/total/forgetful surface.

open import LogOS.Prelude
open import LogOS.LT.Thin2Cat using (Thin2Cat)

open import LogOS.Ports.Valuation.QAdapter using (QAdapter)
open import LogOS.Ports.Valuation.ScaleBoundary using (ScaleBoundary)
open import LogOS.Ports.Valuation.AbstractJoinPrequantale using (ScaleJoinPrequantale)

open import LogOS.Ports.AbstractLandauer.Ledger using (LandauerAssumptions)
import LogOS.Ports.AbstractLandauer2Cat as Landauer2Cat

import LogOS.LT.Ports.Template.Stack2Cat as Template

module LandauerStack2CatLocal
  {ℓObj ℓHomCon ℓHomRel ℓQ : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  (Q : QAdapter ℓQ)
  where

  Scale = ScaleBoundary Q
  JP = ScaleJoinPrequantale Q

  record LandauerStackAssumptions
    : Set (lsuc (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel ⊔ ℓQ))) where
    field
      landauer : LandauerAssumptions C Scale JP

  open LandauerStackAssumptions public

  module Ports (A : LandauerStackAssumptions) =
    Template.SingletonPortStackExports
      (Landauer2Cat.singleton {C = C} (landauer A))

  stack2Cat
    : LandauerStackAssumptions
    → Template.Stack2Cat C
  stack2Cat A =
    Ports.stack2Cat A

  module Port (A : LandauerStackAssumptions) = Ports A

  open Port public using
    ( Displayed
    ; WithPort
    ; forget
    ; baseObj
    ; baseHom
    )
    renaming
      ( stack to LandauerStack
      ; port to landauerPort
      )

open LandauerStack2CatLocal public using
  ( LandauerStackAssumptions
  ; LandauerStack
  ; landauerPort
  ; stack2Cat
  ; Displayed
  ; WithPort
  ; forget
  ; baseObj
  ; baseHom
  )
