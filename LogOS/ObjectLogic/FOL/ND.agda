{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ObjectLogic.FOL.ND where

open import LogOS.Prelude

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)

open import LogOS.ObjectLogic.FOL.Syntax
open import LogOS.ObjectLogic.FOL.Subst

-- Natural deduction for relational FOL (intuitionistic).
-- Contexts are lists; membership is `∈ᶜ` from `Syntax`.

data Deriv {ℓ : Level}
           {Σ₀ : Signature {ℓ}}
           {n  : ℕ}
           (Γ  : Ctx Σ₀ n)
           : Fml Σ₀ n → Set ℓ where

  hyp : ∀ {φ} → φ ∈ᶜ Γ → Deriv Γ φ

  ⊥E  : ∀ {φ} → Deriv Γ ⊥ᶠ → Deriv Γ φ

  ⇒I  : ∀ {φ ψ} → Deriv (φ ∷ Γ) ψ → Deriv Γ (φ ⇒ ψ)
  ⇒E  : ∀ {φ ψ} → Deriv Γ (φ ⇒ ψ) → Deriv Γ φ → Deriv Γ ψ

  ∧I  : ∀ {φ ψ} → Deriv Γ φ → Deriv Γ ψ → Deriv Γ (φ ∧ ψ)
  ∧E₁ : ∀ {φ ψ} → Deriv Γ (φ ∧ ψ) → Deriv Γ φ
  ∧E₂ : ∀ {φ ψ} → Deriv Γ (φ ∧ ψ) → Deriv Γ ψ

  ∨I₁ : ∀ {φ ψ} → Deriv Γ φ → Deriv Γ (φ ∨ ψ)
  ∨I₂ : ∀ {φ ψ} → Deriv Γ ψ → Deriv Γ (φ ∨ ψ)
  ∨E  : ∀ {φ ψ χ}
       → Deriv Γ (φ ∨ ψ)
       → Deriv (φ ∷ Γ) χ
       → Deriv (ψ ∷ Γ) χ
       → Deriv Γ χ

  ∀I  : ∀ {φ : Fml Σ₀ (suc n)} → Deriv (wkCtx Γ) φ → Deriv Γ (All φ)
  ∀E  : ∀ {φ : Fml Σ₀ (suc n)} → Deriv Γ (All φ) → (t : Term n) → Deriv Γ (inst t φ)

  ∃I  : ∀ {φ : Fml Σ₀ (suc n)} → (t : Term n) → Deriv Γ (inst t φ) → Deriv Γ (Ex φ)
  ∃E  : ∀ {φ : Fml Σ₀ (suc n)} {ψ : Fml Σ₀ n}
       → Deriv Γ (Ex φ)
       → Deriv (φ ∷ wkCtx Γ) (wkFml ψ)
       → Deriv Γ ψ
