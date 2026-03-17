{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Host.Sum where

open import LogOS.Host.Level using (Level; _⊔_)

-- Minimal sum type (disjoint union), mirroring std-lib's Data.Sum.

infixr 1 _⊎_

data _⊎_ {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

