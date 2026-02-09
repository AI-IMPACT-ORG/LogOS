{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.All where

-- Power-user umbrella: the full kernel development in one import.
--
-- Prefer `LogOS.Kernel.Surface` (or `LogOS.API.Kernel`) unless you explicitly
-- want the larger namespace.

open import LogOS.Kernel.Surface public

-- Interface-level extras (still no ports/adapters, packs, or domain).
open import LogOS.Kernel.TierCategorical public
open import LogOS.Kernel.GuardedTier public
open import LogOS.Kernel.BudgetedTier public using
  ( BudgetedTier
  ; stepOrderOfBudgetedTier
  ; budgetedTierFromUngradedKernel
  ; budgetedTierFromGradedKernel
  ; module Derived
  )
open import LogOS.Kernel.Tiers public
open import LogOS.Kernel.FromUngradedKernel public renaming (asKernel to asKernelUngraded)
open import LogOS.Kernel.FromGradedKernel public renaming (asKernel to asKernelGraded)

-- Concrete implementations (explicit).
open import LogOS.Kernel.UngradedKernel public using (UngradedKernel)
open import LogOS.Kernel.Graded public using (GradedKernel)
