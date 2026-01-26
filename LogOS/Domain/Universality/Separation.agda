{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.Separation where

open import LogOS.Prelude

open import LogOS.Domain.Universality.ComplexitySpectrum
open import LogOS.Prelude.Product using (Σ; _,_)
open import LogOS.Prelude.Nat using (ℕ)
open import LogOS.Domain.Universality.Core
open import LogOS.Syntax.Prop using (¬_; Dec)
open import LogOS.Domain.Universality.Physics

-- Compatibility between encodings and operator semantics (abstract, model-provided)

record EncodingsCompat {ℓ : Level}
                       (CM : ComplexityModel {ℓ})
                       (EO : EvolOperator {ℓH = ℓ} CoreUCode stepCoreU)
                       : Set (lsuc (lsuc ℓ)) where
  open ComplexityModel CM
  open EvolOperator EO

  -- Verifier acceptance witness: there exists a code/witness and a time bound
  -- such that the verifier runs within that time.
  VerAccepts : Input → Set lzero
  VerAccepts x = Σ ℕ (λ n → Σ CoreUCode (λ w → TimeLeV n (encV x)))

  field
    DetSub : H → Set ℓ
    VerSub : H → Set ℓ
    inDet  : ∀ x → DetSub (embed (encD x))
    inVer  : ∀ x → VerSub (embed (encV x))

    -- Acceptance semantics links verifier complexity to acceptance in H (model-provided).
    AcceptLink : ∀ x → Dec (VerAccepts x)

-- Full separation pack: complexity, operator, physics, compatibility ⇒ separation claim

record SeparationPack {ℓ : Level}
                      (CM : ComplexityModel {ℓ})
                      (EO : EvolOperator {ℓH = ℓ} CoreUCode stepCoreU)
                      (PP : PhysicalPostulates EO)
                      (EC : EncodingsCompat CM EO)
                      : Set (lsuc (lsuc ℓ)) where
  field
    claim : SeparationClaim
