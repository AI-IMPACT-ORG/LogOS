{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.Physics where

open import LogOS.Prelude
open import LogOS.Prelude.Nat using (ℕ)
open import LogOS.Prelude.Product using (Σ; _,_)
open import LogOS.Prelude.Sum using (_⊎_)

open import LogOS.Domain.Universality.Core
open import LogOS.Domain.Universality.ComplexitySpectrum

-- Physical postulates for the time evolution operator

record PhysicalPostulates {ℓ : Level}
                          (EO : EvolOperator {ℓH = ℓ} CoreUCode stepCoreU)
                          : Set (lsuc (lsuc ℓ)) where
  open EvolOperator EO
  field
    -- Locality: evolution in t steps affects only a neighborhood whose size
    -- grows at most polynomially in t (abstractly captured as a Set predicate).
    Locality : Set ℓ

    -- Causality: spacelike separated subsystems evolve independently; encoded
    -- abstractly as a Set predicate (models supply a formalization).
    Causality : Set ℓ

    -- Local unitarity: Op preserves a model-provided norm/inner product locally.
    LocalUnitary : Set ℓ

-- Separation from physics: combine complexity model (Blum-based) and a time
-- evolution operator satisfying physical postulates to assert P≠NP as a Set.
--
-- We make the assumptions explicit and package the claim separately.

record PhysicsSeparationAssumptions {ℓ : Level}
                                    (CM : ComplexityModel {ℓ})
                                    (EO : EvolOperator {ℓH = ℓ} CoreUCode stepCoreU)
                                    (PP : PhysicalPostulates EO)
                                    : Set (lsuc (lsuc ℓ)) where
  open ComplexityModel CM
  open EvolOperator EO
  open PhysicalPostulates PP
  field
    -- Polynomial propagation bound on deterministic encodings (from Locality)
    PolyPropDet : Set ℓ

    -- Superpolynomial resource for verifier encodings (quantum/parallel) consistent
    -- with LocalUnitary + Causality (model declares existence)
    SuperPolyVer : Set ℓ

record PhysicsSeparation {ℓ : Level}
                         (CM : ComplexityModel {ℓ})
                         (EO : EvolOperator {ℓH = ℓ} CoreUCode stepCoreU)
                         (PP : PhysicalPostulates EO)
                         : Set (lsuc (lsuc ℓ)) where
  field
    assumptions : PhysicsSeparationAssumptions CM EO PP

    -- Claim: P≠NP (stated as a Set proposition)
    claim : SeparationClaim

  open PhysicsSeparationAssumptions assumptions public
