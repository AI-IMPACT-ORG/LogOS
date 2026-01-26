{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann where

open import LogOS.Prelude
open import LogOS.Ports.SpectralPack using (SpectralPack)

-- Spectral side for ζ: abstract spectral set with the critical-line predicate

record RiemannSpectral : Set (lsuc lzero) where
  field
    core : SpectralPack lzero

  open SpectralPack core public
