{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Kernel where

-- Narrow import surface: kernels and kernel-level tooling.
--
-- This surface is for:
-- - define kernels and kernel morphisms
-- - use kernel-integrated views (finite/infinite/graded interfaces)
--
-- Not for:
-- - ports/presentations/adapters (use `LogOS.API.PortsAdapters` or `LogOS.API.Architecture`)
-- - curated applications (use `LogOS.Packs.*.Surface`)
--
-- This module intentionally does NOT re-export ports/adapters or domain/packs.

-- Keep the surface usable as a “single import” for downstream work, but avoid
-- re-exporting the full foundations bundle (which can introduce common-name
-- clashes like `to`, `S`, etc in topic-level code). If you want the whole
-- foundations umbrella, import `LogOS.API.Foundation`.
open import LogOS.Prelude public
open import LogOS.Base.Signature public
open import LogOS.Minimal.Adapter public
open import LogOS.Minimal.Con public
open import LogOS.Minimal.View public

-- Kernel definitions + stable kernel tooling surface.
open import LogOS.Kernel.Surface public
open import LogOS.Kernel.TierCategorical public

-- Optional interfaces / concrete kernel implementations (explicit, no tiers umbrella).
open import LogOS.Kernel.GuardedTier public
open import LogOS.Kernel.BudgetedTier public using
  ( BudgetedTier
  ; stepOrderOfBudgetedTier
  ; budgetedTierFromUngradedKernel
  ; budgetedTierFromGradedKernel
  ; module Derived
  )
open import LogOS.Kernel.FromUngradedKernel public renaming (asKernel to asKernelUngraded)
open import LogOS.Kernel.FromGradedKernel public renaming (asKernel to asKernelGraded)
open import LogOS.Kernel.UngradedKernel public using (UngradedKernel)
open import LogOS.Kernel.Graded public using (GradedKernel)

-- Structured namespace access: allow consumers (esp. docs) to refer to
-- `Shape.Code≤`, `Shape.Code≈`, etc without importing `LogOS.Kernel.*` directly.
import LogOS.Kernel.Shape as Shapeₜ
module Shape = Shapeₜ
