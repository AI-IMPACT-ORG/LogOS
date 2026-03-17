{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.SetTheory.ChoiceAxiom where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

-- Set-theoretic Axiom of Choice (AC) in an internal universe `SetU`.
-- (Kuratowski pairs for the graph of a choice function.)
--
-- Note: `_≈_` here is set equality in the object theory, not LT mutual refinement.

PairingAxiom
  : ∀ {ℓ}
    (SetU : Set ℓ)
    (_∈_  : SetU → SetU → Set ℓ)
    (_≈_  : SetU → SetU → Set ℓ)
  → Set ℓ
PairingAxiom SetU _∈_ _≈_ =
  ∀ x y → Σ SetU (λ p → ∀ z → (z ∈ p) ↔ ((z ≈ x) ⊎ (z ≈ y)))

module ChoiceAxiomLocal {ℓ}
         (SetU : Set ℓ)
         (_∈_  : SetU → SetU → Set ℓ)
         (_≈_  : SetU → SetU → Set ℓ)
         (pairing : PairingAxiom SetU _∈_ _≈_)
         where

  -- Unordered pair and singleton, extracted from the Pairing axiom witness.
  pairSet : SetU → SetU → SetU
  pairSet x y = proj₁ (pairing x y)

  singleton : SetU → SetU
  singleton x = pairSet x x

  -- Kuratowski ordered pair: ⟨x , y⟩ = {{x} , {x , y}}
  opair : SetU → SetU → SetU
  opair x y = pairSet (singleton x) (pairSet x y)

  GraphSet : SetU → SetU → SetU → Set ℓ
  GraphSet f x y = opair x y ∈ f

  -- A (possibly partial) functional graph restricted to a family X:
  -- - domain is contained in X (no pairs for indices outside X)
  -- - total on X (each x∈X has a chosen element y∈x)
  -- - functional on X (unique output up to ≈)
  ChoiceFunctionOn : SetU → SetU → Set ℓ
  ChoiceFunctionOn f X =
    (∀ x y → GraphSet f x y → x ∈ X)
    × (∀ x → x ∈ X → Σ SetU (λ y → GraphSet f x y × (y ∈ x)))
    × (∀ x y₁ y₂ → GraphSet f x y₁ → GraphSet f x y₂ → y₁ ≈ y₂)

  -- AC: every family of nonempty sets has a choice function.
  AxiomOfChoice : Set ℓ
  AxiomOfChoice =
    ∀ X →
      (∀ x → x ∈ X → Σ SetU (λ y → y ∈ x))
      → Σ SetU (λ f → ChoiceFunctionOn f X)
