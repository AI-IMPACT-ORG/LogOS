{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Globalise where

-- Optional global coherence (antisymmetry-based strictification) for distributed boundaries.
-- (“Classical limit” remains an internal label here; the mechanised content is an explicit extensional/posetal collapse, not classical logic/LEM.)
--
-- In many shared/distributed semantics designs the boundary carrier is
-- function-shaped (e.g. `I → O`). Mathematical correspondences are often
-- proven pointwise (per index), but upgrading pointwise equality to strict
-- propositional equality of functions is a separate principle
-- (function extensionality; judgmental equality is meta-level).
--
-- This module packages that principle as an explicit port-level assumption.
--
-- This is the top rung of the extensionality ladder:
-- pointwise equalities become strict equalities only here, not in the default
-- `FunPreorder`/`KernelHom` semantics.

open import LogOS.Prelude
record DependentGlobalise {ℓI ℓX : Level} (I : Set ℓI) (X : I → Set ℓX)
  : Set (lsuc (ℓI ⊔ ℓX)) where
  field
    globaliseᵈ : {f g : (i : I) → X i} → (∀ i → f i ≡ g i) → f ≡ g

open DependentGlobalise public
-- Uniform variant: a constant-family special case of dependent global coherence.
record Globalise {ℓI ℓX : Level} (I : Set ℓI) (X : Set ℓX)
  : Set (lsuc (ℓI ⊔ ℓX)) where
  field
    coh : DependentGlobalise I (λ _ → X)

  globalise : {f g : I → X} → (∀ i → f i ≡ g i) → f ≡ g
  globalise = globaliseᵈ coh

open Globalise public
