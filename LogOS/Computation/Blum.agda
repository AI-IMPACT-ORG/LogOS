{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.Blum where

open import LogOS.Prelude
open import LogOS.Computation.Core
open import LogOS.Syntax.Prop using (⊥; ¬_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- Blum-like structure (schematic). Models supply decidability and domain facts.

record Blum {ℓ : Level} (Code : Set ℓ) : Set (lsuc (lsuc ℓ)) where
  field
    Comp  : Computation Code
    TimeLe : ℕ → Code → Set ℓ                 -- time relation (e.g., Halts (iterate n code))
    Domain : Code → Set ℓ                     -- halting domain
    total  : ∀ c → Domain c → Σ ℕ (λ n → TimeLe n c)
    dec    : ∀ n c → TimeLe n c ⊎ ¬ (TimeLe n c)
