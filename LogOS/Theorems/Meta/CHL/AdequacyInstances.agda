{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.AdequacyInstances where

-- Generic helper constructors for CHL completeness surfaces.
--
-- Concrete adequacy instances belong in application/pack layers
-- (for example: `LogOS.Packs.UniversalIR.CHLAdequacyInstances`).

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel using (Kernel)
import LogOS.Theorems.Meta.CHL.Completeness as Complete
import LogOS.Theorems.Meta.CHL.Capstone as Capstone

module ForKernel
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where
  module Co = Complete.For K
  module Cap = Capstone.For K

  capstone-complete
    : (A : Co.BoundaryAdequacy)
    → Cap.CapstoneComplete A
  capstone-complete = Cap.capstone-complete

  capstone-complete-budget
    : (B : Co.Budget)
    → (A : Co.BudgetedAdequacy B)
    → Cap.CapstoneCompleteBudget B A
  capstone-complete-budget B A = Cap.capstone-complete-budget A
