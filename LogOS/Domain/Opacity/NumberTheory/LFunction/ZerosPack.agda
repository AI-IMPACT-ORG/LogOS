{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.NumberTheory.LFunction.ZerosPack where

open import LogOS.Prelude

open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann

-- Guardless GRH predicate for a given spectral adapter:
-- every nontrivial zero lies on the line.

GRH_Without_Vacuity_Guards : (RS : RiemannSpectral) → Set
GRH_Without_Vacuity_Guards RS =
  ∀ s → RiemannSpectral.NontrivialZero RS s → RiemannSpectral.OnLine RS s
