{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.UniversalIR.CHLAdequacyInstances where

-- Concrete CHL adequacy instances for the UniversalIR observed-kernel route.

open import LogOS.Prelude

open import LogOS.UniversalIR.ObservedKernel as Obs
import LogOS.Theorems.Meta.CHL.Completeness as Complete
import LogOS.Theorems.Meta.CHL.Capstone as Capstone
import LogOS.Theorems.Meta.CHL.AdequacyInstances as Generic

module ForObservedKit (K : ObsKit) where
  module OK = Obs.ForObsKit K
  module Co = Complete.For OK.ObsKernel
  module Cap = Capstone.For OK.ObsKernel
  module Gen = Generic.ForKernel OK.ObsKernel
  module CP = OK.CP

  -- Full observation budget (all boundary observations are allowed).
  fullBudget : Co.Budget
  fullBudget _ = Topℓ

  -- Boundary adequacy is immediate because in this kernel:
  -- Sat_H_bnd p c  ≡  p ⊑ c
  -- and to∂ is identity on observations.
  boundaryAdequacy : Co.BoundaryAdequacy
  boundaryAdequacy =
    record
      { reflect = λ ent → ent _ CP.refl
      }

  -- Budgeted variant (for the full budget) is equally immediate.
  fullBudgetAdequacy : Co.BudgetedAdequacy fullBudget
  fullBudgetAdequacy =
    record
      { reflect = λ ent → ent _ ttℓ CP.refl
      }

  capstone-complete : Cap.CapstoneComplete boundaryAdequacy
  capstone-complete = Gen.capstone-complete boundaryAdequacy

  capstone-complete-budget
    : Cap.CapstoneCompleteBudget fullBudget fullBudgetAdequacy
  capstone-complete-budget = Gen.capstone-complete-budget fullBudget fullBudgetAdequacy

-- Concrete exported instance: UniversalIR code observation kit.
module CodeObsKit = ForObservedKit Obs.CodeObsKit
