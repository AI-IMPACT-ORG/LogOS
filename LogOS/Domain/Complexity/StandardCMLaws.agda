{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.StandardCMLaws where

open import LogOS.Prelude

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)
open import Data.NatOrder using (_≤ℕ_)

open import LogOS.Computation.Blum using (Blum)

open import LogOS.Domain.Universality.Core using (ToyUCode)
open import LogOS.Domain.Universality.ComplexitySpectrum as CS
open import LogOS.Domain.Complexity.Model as CM

-- Additional “soundness” laws for a `StandardCM` model.
--
-- These are intentionally kept as *separate* records so existing toy/demo
-- models remain valid, but domains that want classical alignment can demand
-- these laws explicitly.

module For {ℓ : Level} (M : CM.StandardCM {ℓ}) where

  private
    CM₀ = CM.StandardCM.base M

  module C = CS.ComplexityModel CM₀

  -- 1) Nondegeneracy for Blum/TimeLe: encodings must land in the halting domain,
  -- so “TimeLe always false / Domain empty” cannot be used as a “meaningful model”.
  record EncodingsInDomain : Set (lsuc (lsuc ℓ)) where
    field
      domD  : ∀ x → Blum.Domain C.BlumD (C.encD x)
      domV  : ∀ x → Blum.Domain C.BlumV (C.encV x)
      domVW : ∀ x w → Blum.Domain C.BlumV (CM.StandardCM.encVW M x w)

    -- Derived: each encoding has *some* time witness.
    haltsD : ∀ x → Σ ℕ (λ n → Blum.TimeLe C.BlumD n (C.encD x))
    haltsD x = Blum.total C.BlumD (C.encD x) (domD x)

    haltsV : ∀ x → Σ ℕ (λ n → Blum.TimeLe C.BlumV n (C.encV x))
    haltsV x = Blum.total C.BlumV (C.encV x) (domV x)

    haltsVW : ∀ x w → Σ ℕ (λ n → Blum.TimeLe C.BlumV n (CM.StandardCM.encVW M x w))
    haltsVW x w = Blum.total C.BlumV (CM.StandardCM.encVW M x w) (domVW x w)

  -- 2) Reasonable size: relate `size : Input → ℕ` to an explicit encoding-length
  -- metric `codeSize : ToyUCode → ℕ` by polynomial bounds.
  --
  -- This is the standard “all reasonable size measures are poly-related” law,
  -- and it rules out “size := fuel” unless fuel is itself polynomially related
  -- to the chosen encoding length.
  record ReasonableSize : Set (lsuc (lsuc ℓ)) where
    field
      codeSize : ToyUCode → ℕ

      size≤polyCode : Σ (ℕ → ℕ) (λ p →
        C.poly p × (∀ x → C.size x ≤ℕ p (codeSize (C.encD x))))

      code≤polySize : Σ (ℕ → ℕ) (λ p →
        C.poly p × (∀ x → codeSize (C.encD x) ≤ℕ p (C.size x)))
