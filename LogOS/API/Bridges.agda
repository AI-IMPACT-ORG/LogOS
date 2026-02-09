{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Bridges where

-- Canonical bridge surface: relation-safe connectors between core layers.
--
-- This surface is for:
-- - tier alignment (S/H/G/R) and tier-categorical views,
-- - kernel shape bridges (graded/ungraded -> kernel),
-- - flow/endomap bridges (hom + endo + sub-2-category wrappers),
-- - process-limit bridges (`run∞` + continuity-marked morphisms).
--
-- This module keeps existing APIs intact and exposes only already-defined
-- bridge constructs in one place.

open import LogOS.Prelude public
open import LogOS.Base.Signature public
open import LogOS.Minimal.Adapter public
open import LogOS.Minimal.Con public
open import LogOS.Minimal.View public

-- Tier alignment and categorification.
open import LogOS.Kernel.Tiers public
open import LogOS.Kernel.TierCategorical public

-- Kernel representation bridges.
open import LogOS.Kernel.FromUngradedKernel public renaming (asKernel to asKernelUngraded)
open import LogOS.Kernel.FromGradedKernel public renaming (asKernel to asKernelGraded)

-- Boundary flow bridges.
open import LogOS.Kernel.Endo public
open import LogOS.Kernel.Hom public
open import LogOS.Kernel.Hom2Cat public
open import LogOS.Kernel.Hom2Cat.FlowSub2Cat public
import LogOS.Kernel.UngradedKernel.EndoCore as UngradedEndoCore
import LogOS.Kernel.UngradedKernel.EndoRelative as UngradedEndoRelative

-- Process-limit analog of flow-preserving morphism packaging.
import LogOS.Computation.ProcessLimit as ProcessLimitₐ
import LogOS.Computation.ProcessLimitSub2Cat as ProcessLimitSub2Catₐ

module ProcessLimit = ProcessLimitₐ
module ProcessLimitSub2Cat = ProcessLimitSub2Catₐ
