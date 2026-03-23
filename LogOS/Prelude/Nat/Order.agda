{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Prelude.Nat.Order where

-- Constructive natural-number order used by multiple higher layers.

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ; zero; suc)

infix 4 _≤ℕ_
data _≤ℕ_ : ℕ → ℕ → Set lzero where
  z≤n : ∀ {n} → zero ≤ℕ n
  s≤s : ∀ {m n} → m ≤ℕ n → suc m ≤ℕ suc n

≤ℕ-refl : ∀ {n} → n ≤ℕ n
≤ℕ-refl {zero} = z≤n
≤ℕ-refl {suc n} = s≤s ≤ℕ-refl

≤ℕ-trans : ∀ {a b c} → a ≤ℕ b → b ≤ℕ c → a ≤ℕ c
≤ℕ-trans z≤n _ = z≤n
≤ℕ-trans (s≤s ab) (s≤s bc) = s≤s (≤ℕ-trans ab bc)
