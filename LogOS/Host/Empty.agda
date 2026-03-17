{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Host.Empty where

-- Minimal empty type surface (std-lib compatible name).
--
-- This belongs in the Host layer so higher layers (Prelude/Syntax/…) can
-- depend on it without inverting the layering discipline.

open import LogOS.Host.Level  using (Level)

data ⊥ {ℓ : Level} : Set ℓ where

⊥-elim : ∀ {ℓ₁ ℓ₂ : Level} {A : Set ℓ₂} → ⊥ {ℓ₁} → A
⊥-elim ()
