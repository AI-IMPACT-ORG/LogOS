{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
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

    -- Encode a (x,w) verifier input pair into a single ToyUCode for the verifier
    encVW : CS.ComplexityModel.Input base → ToyUCode → ToyUCode

    -- Size for witnesses
    wsize : ToyUCode → ℕ

  -- Re-export common pieces for convenience
  open CS.ComplexityModel base public
