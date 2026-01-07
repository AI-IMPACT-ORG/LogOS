{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Syntax.Eq where

-- Decode-level equality aliases for a given Kernel.
-- This helps keep meta-level ≡ distinct from the intended object-level
-- equality induced by decode.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

module ForKernel {ℓ : Level}
                 {Sig : LogOSSignature ℓ}
                 {Q   : QAdapter ℓ}
                 (K   : Kernel Sig Q) where
  open Kernel K

  infix 4 _≃K_
  _≃K_ : Code → Code → Set ℓ
  γ₁ ≃K γ₂ = decode γ₁ ≡ decode γ₂

  refl≃K : ∀ γ → γ ≃K γ
  refl≃K γ = refl

  sym≃K  : ∀ {γ₁ γ₂} → γ₁ ≃K γ₂ → γ₂ ≃K γ₁
  sym≃K = sym

  trans≃K : ∀ {γ₁ γ₂ γ₃} → γ₁ ≃K γ₂ → γ₂ ≃K γ₃ → γ₁ ≃K γ₃
  trans≃K = trans

