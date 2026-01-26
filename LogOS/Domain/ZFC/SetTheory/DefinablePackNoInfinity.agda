{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.SetTheory.DefinablePackNoInfinity where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Syntax.Prop using (_↔_; ¬_)
open import LogOS.Domain.ZFC.SetTheory.ChoiceAxiom as AC using (AxiomOfChoice)

-- Same as `DefinablePack.ZFAxiomsᵈ` but *without* Infinity.
-- This lets us add Infinity as a separate upgrade derived from LogOS fixed-point
-- structure (ω ≈ Step ω) rather than baking it in as a primitive field.

record ZFAxiomsᵈ-NoInf {ℓ}
                      {Sig : LogOSSignature ℓ}
                      {Q   : QAdapter ℓ}
                      (K   : Kernel Sig Q)
                      : Set (lsuc (lsuc ℓ)) where
  open Kernel K
  infix 4 _∈_ _≈_
  field
    SetU   : Set ℓ
    _∈_    : SetU → SetU → Set ℓ
    _≈_    : SetU → SetU → Set ℓ
    refl≈  : ∀ x → x ≈ x
    sym≈   : ∀ {x y} → x ≈ y → y ≈ x
    trans≈ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

    ⟦_⟧     : Code → SetU
    by-decode≈ : ∀ {γ δ} → decode γ ≡ decode δ → ⟦ γ ⟧ ≈ ⟦ δ ⟧

    extensionality : ∀ x y → (∀ z → (z ∈ x) ↔ (z ∈ y)) → x ≈ y
    mem-ext : ∀ {x y} → x ≈ y → ∀ z → (z ∈ x) ↔ (z ∈ y)
    mem-congL : ∀ {x y} → x ≈ y → ∀ z → (x ∈ z) ↔ (y ∈ z)

    empty : Σ SetU (λ e → ∀ z → ¬ (z ∈ e))
    pairing : ∀ x y → Σ SetU (λ p → ∀ z → (z ∈ p) ↔ ((z ≈ x) ⊎ (z ≈ y)))
    union  : ∀ x → Σ SetU (λ u → ∀ z → (z ∈ u) ↔ (Σ SetU (λ y → (y ∈ x) × (z ∈ y))))
    powerset : ∀ x → Σ SetU (λ p → ∀ z → (z ∈ p) ↔ (∀ w → w ∈ z → w ∈ x))

    zeroS : SetU
    zeroS-empty : ∀ z → ¬ (z ∈ zeroS)
    succ  : SetU → SetU
    mem-succ↔ : ∀ x z → (z ∈ succ x) ↔ ((z ∈ x) ⊎ (z ≈ x))

    separationᵈ
      : (γ : Code) → ∀ x →
        Σ SetU (λ y → ∀ z → (z ∈ y) ↔ ((z ∈ x) × (z ∈ ⟦ γ ⟧)))

    Graph : Code → SetU → SetU → Set ℓ

  -- “Functional” means: the graph is single-valued (up to `≈`).
  FunctionalGraph : (Graph : SetU → SetU → Set ℓ) → Set ℓ
  FunctionalGraph Graph = ∀ u z₁ z₂ → Graph u z₁ → Graph u z₂ → z₁ ≈ z₂

  field
    replacementᵈ
      : (γ : Code) → FunctionalGraph (Graph γ) → ∀ x →
        Σ SetU (λ y → ∀ z → (z ∈ y) ↔ (Σ SetU (λ u → (u ∈ x) × Graph γ u z)))

    foundation : ∀ x → (x ≈ zeroS) ⊎ (Σ SetU (λ y → y ∈ x × (∀ z → z ∈ x → ¬ (z ∈ y))))

record ZFCAxiomsᵈ-NoInf {ℓ}
                       {Sig : LogOSSignature ℓ}
                       {Q   : QAdapter ℓ}
                       (K   : Kernel Sig Q)
                       : Set (lsuc (lsuc ℓ)) where
  field
    zf : ZFAxiomsᵈ-NoInf K

  open ZFAxiomsᵈ-NoInf zf public

  field
    AC : AC.AxiomOfChoice SetU _∈_ _≈_ pairing
