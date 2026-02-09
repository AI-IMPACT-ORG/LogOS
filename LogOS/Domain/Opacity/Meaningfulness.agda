{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Meaningfulness where

open import LogOS.Prelude
open import LogOS.Theorems.Meta.Guards using (NonEmptyPred; NotTopPred)

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)

-- Vacuity guards for GRH/RH:
--
-- These do not change any GRH theorems; they rule out degenerate instantiations
-- where the statement becomes vacuous (no nontrivial zeros) or tautological
-- (OnLine ≡ ⊤).

record VacuityGuards (RS : RiemannSpectral) : Set₁ where
  open RiemannSpectral RS
  field
    hasNontrivialZero : NonEmptyPred Spectral NontrivialZero
    onLineNotTop      : NotTopPred Spectral OnLine
