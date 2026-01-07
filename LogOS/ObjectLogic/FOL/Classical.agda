{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ObjectLogic.FOL.Classical where

open import LogOS.Prelude

open import LogOS.ObjectLogic.FOL.Syntax

-- Optional classical axiom schemas, expressed as axiom predicates.
--
-- These are intentionally *not* assumed by the core ND calculus (`FOL.ND`).
-- They can be supplied as “extra axioms” via `FOL.NDTheory.DerivAx`.

module _ {ℓ : Level} {Σ₀ : Signature {ℓ}} where

  data LEM : ∀ {n} → Fml Σ₀ n → Set ℓ where
    lem : ∀ {n} (φ : Fml Σ₀ n) → LEM (φ ∨ Not φ)

  data DNE : ∀ {n} → Fml Σ₀ n → Set ℓ where
    dne : ∀ {n} (φ : Fml Σ₀ n) → DNE ((Not (Not φ)) ⇒ φ)
