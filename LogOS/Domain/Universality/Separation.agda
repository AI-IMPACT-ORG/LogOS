{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.Separation where

open import LogOS.Prelude

open import LogOS.Domain.Universality.ComplexitySpectrum
open import Data.Product using (Σ; _,_)
open import Data.Nat using (ℕ)
open import LogOS.Domain.Universality.Core
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import LogOS.Syntax.Prop using (¬_)
open import LogOS.Domain.Universality.Physics

-- Compatibility between encodings and operator semantics (abstract, model-provided)

record EncodingsCompat {ℓ : Level}
                       (CM : ComplexityModel {ℓ})
                       (EO : EvolOperator {ℓH = ℓ} ToyUCode stepToyU)
                       : Set (lsuc (lsuc ℓ)) where
  open ComplexityModel CM
  open EvolOperator EO
  field
    DetSub : H → Set ℓ
    VerSub : H → Set ℓ
    inDet  : ∀ x → DetSub (embed (encD x))
    inVer  : ∀ x → VerSub (embed (encV x))
    -- Acceptance semantics links verifier complexity to acceptance in H (model-provided)
    AcceptLink : ∀ x → (Σ ℕ (λ n → Σ ToyUCode (λ w → TimeLeV n (encV x)))) ⊎ ¬ (Σ ℕ (λ n → Σ ToyUCode (λ w → TimeLeV n (encV x))))

-- Full separation pack: complexity, operator, physics, compatibility ⇒ separation claim

record SeparationPack {ℓ : Level}
                      (CM : ComplexityModel {ℓ})
                      (EO : EvolOperator {ℓH = ℓ} ToyUCode stepToyU)
                      (PP : PhysicalPostulates EO)
                      (EC : EncodingsCompat CM EO)
                      : Set (lsuc (lsuc ℓ)) where
  field
    claim : SeparationClaim
