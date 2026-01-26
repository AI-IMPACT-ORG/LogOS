{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.SpectralFromFacts where

open import LogOS.Prelude

open import LogOS.Algebra.Ring
open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann as RZ
open import LogOS.Domain.Opacity.NumberTheory.LFunction.RiemannFacts
open import LogOS.Theorems.Meta.GRHBridge as GRHB

-- Build a generic SpectralPack directly from classical Riemann facts.

SpectralFromFacts : (F : RiemannFacts) → GRHB.SpectralPack lzero
SpectralFromFacts F =
  record
    { Spectral       = Ring.Carrier (RiemannFacts.Rℂ F)
    ; OnLine         = λ s → RiemannFacts.Re F s ≡ RiemannFacts.half F
    ; NontrivialZero = λ s → RiemannFacts.XiZero F s × RiemannFacts.InStrip F s
    }
