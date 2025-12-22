{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.Growth where

open import Data.Nat using (ℕ; suc)
open import LogOS.Prelude

open import LogOS.Domain.Universality.Core
open import LogOS.Domain.Universality.ComplexitySpectrum

-- Simplified growth scaffolding: enough structure to compile and wire examples.

record LocalLightCone (EO : EvolOperator {ℓH = lzero} ToyUCode stepToyU) : Set where
  field
    LightCone : ⊤

record PolyBoundDet (CM : ComplexityModel {lzero}) (EO : EvolOperator {ℓH = lzero} ToyUCode stepToyU) (LC : LocalLightCone EO) : Set where
  field
    witnessP : ⊤

record SuperPolyVer (CM : ComplexityModel {lzero}) (EO : EvolOperator {ℓH = lzero} ToyUCode stepToyU) (LC : LocalLightCone EO) : Set where
  field
    witnessS : ⊤

mkSeparationHyps : (CM : ComplexityModel {lzero}) (EO : EvolOperator {ℓH = lzero} ToyUCode stepToyU) (LC : LocalLightCone EO)
                 → PolyBoundDet CM EO LC → SuperPolyVer CM EO LC → SeparationHypotheses CM EO
mkSeparationHyps CM EO LC PBD SPV =
  record { SpecPolyBound = Topℓ
         ; SpecSuperPoly = Topℓ
         }
