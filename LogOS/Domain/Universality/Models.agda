{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.Models where

open import LogOS.Prelude

open import LogOS.Domain.Universality.Core
open import LogOS.Domain.Universality.ComplexitySpectrum
open import LogOS.Domain.Universality.Physics
open import LogOS.Domain.Universality.Separation

-- A clean bundle that layers the computational pieces:
-- Complexity model, operator, physics, and encoding compatibility
-- with optional hypotheses packs.

record CompModelsPack {ℓ : Level}
                      (CM : ComplexityModel {ℓ})
                      (EO : EvolOperator {ℓH = ℓ} ToyUCode stepToyU)
                      (PP : PhysicalPostulates EO)
                      (EC : EncodingsCompat CM EO)
                      : Set (lsuc (lsuc ℓ)) where
  field
    -- Optional: spectral growth hypotheses (model-provided)
    growth  : SeparationHypotheses CM EO

    -- Physics side: realizes a physics-based separation
    phys    : PhysicsSeparation CM EO PP

    -- Encodings/complexity/operator composed into a pack
    sepPack : SeparationPack CM EO PP EC

  open SeparationHypotheses growth public
  open PhysicsSeparation phys public
  open SeparationPack sepPack public
