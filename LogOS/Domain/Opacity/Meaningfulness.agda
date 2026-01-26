{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Meaningfulness where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)
open import LogOS.Prelude.Product using (Σ; _,_)

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)

-- Vacuity guards for GRH/RH:
--
-- These do not change any GRH theorems; they rule out degenerate instantiations
-- where the statement becomes vacuous (no nontrivial zeros) or tautological
-- (OnLine ≡ ⊤).

record VacuityGuards (RS : RiemannSpectral) : Set₁ where
  open RiemannSpectral RS
  field
    hasNontrivialZero : Σ Spectral NontrivialZero
    onLineNotTop      : Σ Spectral (λ s → ¬ OnLine s)
