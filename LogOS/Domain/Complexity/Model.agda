{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.Model where

open import LogOS.Prelude
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)

open import LogOS.Domain.Universality.Core
open import LogOS.Domain.Universality.ComplexitySpectrum as CS

-- Standard, industry-aligned complexity model: extend the generic ComplexityModel
-- with explicit witness encoding and size functions to talk about NP cleanly.

record StandardCM {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
  field
    base  : CS.ComplexityModel {ℓ}

    -- Encode a (x,w) verifier input pair into a single CoreUCode for the verifier
    encVW : CS.ComplexityModel.Input base → CoreUCode → CoreUCode

    -- Size for witnesses
    wsize : CoreUCode → ℕ

  -- Re-export common pieces for convenience
  open CS.ComplexityModel base public

-- Optional soundness laws for StandardCM (merged from StandardCMLaws).
module StandardCMLaws where
  open import Data.Nat using (ℕ)
  open import Data.Product using (Σ; _,_)
  open import Data.NatOrder using (_≤ℕ_)

  open import LogOS.Computation.Blum using (Blum)
  open import LogOS.Domain.Universality.Core using (CoreUCode)
  open import LogOS.Domain.Universality.ComplexitySpectrum as CS

  module For {ℓ : Level} (M : StandardCM {ℓ}) where

    private
      CM₀ = StandardCM.base M

    module C = CS.ComplexityModel CM₀

    record EncodingsInDomain : Set (lsuc (lsuc ℓ)) where
      field
        domD  : ∀ x → Blum.Domain C.BlumD (C.encD x)
        domV  : ∀ x → Blum.Domain C.BlumV (C.encV x)
        domVW : ∀ x w → Blum.Domain C.BlumV (StandardCM.encVW M x w)

      haltsD : ∀ x → Σ ℕ (λ n → Blum.TimeLe C.BlumD n (C.encD x))
      haltsD x = Blum.total C.BlumD (C.encD x) (domD x)

      haltsV : ∀ x → Σ ℕ (λ n → Blum.TimeLe C.BlumV n (C.encV x))
      haltsV x = Blum.total C.BlumV (C.encV x) (domV x)

      haltsVW : ∀ x w → Σ ℕ (λ n → Blum.TimeLe C.BlumV n (StandardCM.encVW M x w))
      haltsVW x w = Blum.total C.BlumV (StandardCM.encVW M x w) (domVW x w)

    record ReasonableSize : Set (lsuc (lsuc ℓ)) where
      field
        codeSize : CoreUCode → ℕ

        size≤polyCode : Σ (ℕ → ℕ) (λ p →
          C.poly p × (∀ x → C.size x ≤ℕ p (codeSize (C.encD x))))

        code≤polySize : Σ (ℕ → ℕ) (λ p →
          C.poly p × (∀ x → codeSize (C.encD x) ≤ℕ p (C.size x)))
