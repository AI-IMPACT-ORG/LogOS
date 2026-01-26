{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.LogicKernel where

-- ============================================================================
-- LogOS API — LOGICKERNEL VIEW
--
-- Exposes the Curry–Howard–Lambek “single system” interface:
-- a shared S/H/code shape + a (parameterised) guarded tier, together with the
-- canonical saturation-level endomap DSL.
--
-- This module introduces no axioms/postulates.
-- ============================================================================

open import LogOS.Prelude public
open import LogOS.Kernel.LogicKernel.All public

