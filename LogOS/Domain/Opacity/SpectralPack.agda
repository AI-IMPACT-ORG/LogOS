{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.SpectralPack where

open import LogOS.Prelude
open import LogOS.Domain.Opacity.NumberTheory.LFunction.Riemann using (RiemannSpectral)
import LogOS.Theorems.Meta.GRHBridge as GRHB

-- Shared helper: cast a Riemann spectral pack into the nucleus-friendly record.
RStoSP : RiemannSpectral → GRHB.SpectralPack lzero
RStoSP RS = record
  { Spectral       = RiemannSpectral.Spectral RS
  ; OnLine         = RiemannSpectral.OnLine RS
  ; NontrivialZero = RiemannSpectral.NontrivialZero RS
  }
