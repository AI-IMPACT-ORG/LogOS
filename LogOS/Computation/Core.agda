{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.Core where

open import LogOS.Prelude
open import LogOS.Minimal.Con using (ConPoset; MonoOn)

-- Minimal computation interface: a code carrier with a total step.

record Computation {ℓ : Level} (Code : Set ℓ) : Set (lsuc ℓ) where
  field
    Step  : Code → Code
    Halts : Code → Set ℓ         -- halting predicate (model-chosen)

open Computation public

iterate : ∀ {ℓ Code} → Computation {ℓ} Code → ℕ → Code → Code
iterate C zero    c = c
iterate C (suc n) c = iterate C n (Computation.Step C c)

iterate-+
  : ∀ {ℓ Code}
    (C : Computation {ℓ} Code)
    (m n : ℕ)
    (c : Code)
  → iterate C (m + n) c ≡ iterate C n (iterate C m c)
iterate-+ C zero    n c = refl
iterate-+ C (suc m) n c = iterate-+ C m n (Computation.Step C c)

-- Iteration preserves monotonicity on a constraint poset.
--
-- This is a small but reusable bridge between operational iteration (`iterate`)
-- and order-theoretic reasoning (preorders on states).

iterate-mono
  : ∀ {ℓ}
    (CP : ConPoset ℓ)
    (f : ConPoset.Con CP → ConPoset.Con CP)
    (mono : MonoOn CP f)
  → ∀ n {x y}
  → ConPoset._⊑_ CP x y
  → ConPoset._⊑_ CP (iterate (record { Step = f ; Halts = λ _ → Topℓ }) n x)
                     (iterate (record { Step = f ; Halts = λ _ → Topℓ }) n y)
iterate-mono CP f mono zero    p = p
iterate-mono CP f mono (suc n) p = iterate-mono CP f mono n (mono p)
