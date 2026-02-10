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
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary)
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

  fullBudget : Co.Budget
  fullBudget = Co.fullBudget

  boundaryAdequacy-from-reflect
    : (∀ {c d}
       → (∀ w
           → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) c
           → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) d)
       → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K)) c d)
    → Co.BoundaryAdequacy
  boundaryAdequacy-from-reflect = Co.mkBoundaryAdequacy

  budgetedAdequacy-from-reflect
    : ∀ {B : Co.Budget}
    → (∀ {c d}
       → (∀ w
           → B w
           → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) c
           → Kernel.Sat_H_bnd K (LogOSSignature.to∂ Sig w) d)
       → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K)) c d)
    → Co.BudgetedAdequacy B
  budgetedAdequacy-from-reflect = Co.mkBudgetedAdequacy

  fullBudgetAdequacy-from-boundary
    : Co.BoundaryAdequacy
    → Co.BudgetedAdequacy fullBudget
  fullBudgetAdequacy-from-boundary = Co.boundary→budget-full

  boundaryAdequacy-from-fullBudget
    : Co.BudgetedAdequacy fullBudget
    → Co.BoundaryAdequacy
  boundaryAdequacy-from-fullBudget = Co.budget-full→boundary

  capstone-complete
    : (A : Co.BoundaryAdequacy)
    → Cap.CapstoneComplete A
  capstone-complete = Cap.capstone-complete

  capstone-complete-full
    : (A : Co.BoundaryAdequacy)
    → Cap.CapstoneCompleteBudget fullBudget (fullBudgetAdequacy-from-boundary A)
  capstone-complete-full A = Cap.capstone-complete-budget (fullBudgetAdequacy-from-boundary A)

  capstone-complete-budget
    : (B : Co.Budget)
    → (A : Co.BudgetedAdequacy B)
    → Cap.CapstoneCompleteBudget B A
  capstone-complete-budget B A = Cap.capstone-complete-budget A
