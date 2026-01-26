{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.All where

-- Convenience re-export: the `LogicKernel` interface, bridges from existing
-- kernels, and the shared saturation-level endomap DSL.

open import LogOS.Kernel.LogicKernel public
open import LogOS.Kernel.LogicKernel.GuardedTier public
open import LogOS.Kernel.LogicKernel.BudgetedTier public
open import LogOS.Kernel.LogicKernel.VacuityGuards public
open import LogOS.Kernel.LogicKernel.FromKernel public
  renaming (asLogicKernel to asLogicKernelK)
open import LogOS.Kernel.LogicKernel.FromGradedKernel public
  renaming (asLogicKernel to asLogicKernelG)
open import LogOS.Kernel.LogicKernel.Endo public
open import LogOS.Kernel.LogicKernel.EndoRelative public
open import LogOS.Kernel.LogicKernel.Boundary public
open import LogOS.Kernel.LogicKernel.TensorDSL public
open import LogOS.Kernel.LogicKernel.Hom public
open import LogOS.Kernel.LogicKernel.Hom2Cat public
open import LogOS.Kernel.LogicKernel.Reindex public
open import LogOS.Kernel.LogicKernel.HomOverSig public
open import LogOS.Kernel.LogicKernel.Tiers public
open import LogOS.Kernel.LogicKernel.Hom.FromKernel public
  renaming (asLogicKernelHom to asLogicKernelHomK)
open import LogOS.Kernel.LogicKernel.Hom.FromGradedKernel public
  renaming (asLogicKernelHom to asLogicKernelHomG)
