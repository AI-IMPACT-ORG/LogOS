{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ObjectLogic.FOL.Syntax where

open import LogOS.Prelude

open import Data.Fin using (Fin; fzero; fsuc)
open import Data.List using (List; []; _∷_)

-- Pure relational first-order syntax (no function symbols).
-- Terms are variables (de Bruijn, well-scoped via `Fin n`).

record Signature {ℓ : Level} : Set (lsuc ℓ) where
  field
    PredSym : Set ℓ         -- unary predicate symbols
    RelSym₂ : Set ℓ         -- binary relation symbols

open Signature public

Term : ℕ → Set
Term n = Fin n

data Fml {ℓ : Level} (Σ : Signature {ℓ}) : ℕ → Set ℓ where
  ⊥ᶠ     : ∀ {n} → Fml Σ n
  pred   : ∀ {n} → PredSym Σ → Term n → Fml Σ n
  rel₂   : ∀ {n} → RelSym₂ Σ → Term n → Term n → Fml Σ n
  _⇒_    : ∀ {n} → Fml Σ n → Fml Σ n → Fml Σ n
  _∧_    : ∀ {n} → Fml Σ n → Fml Σ n → Fml Σ n
  _∨_    : ∀ {n} → Fml Σ n → Fml Σ n → Fml Σ n
  All    : ∀ {n} → Fml Σ (suc n) → Fml Σ n
  Ex     : ∀ {n} → Fml Σ (suc n) → Fml Σ n

infixr 5 _⇒_
infixr 6 _∧_
infixr 5 _∨_

Not : ∀ {ℓ} {Σ : Signature {ℓ}} {n} → Fml Σ n → Fml Σ n
Not φ = φ ⇒ ⊥ᶠ

Iff : ∀ {ℓ} {Σ : Signature {ℓ}} {n} → Fml Σ n → Fml Σ n → Fml Σ n
Iff φ ψ = (φ ⇒ ψ) ∧ (ψ ⇒ φ)

Topᶠ : ∀ {ℓ} {Σ : Signature {ℓ}} {n} → Fml Σ n
Topᶠ = Not ⊥ᶠ

-- Contexts and membership (for proof systems).

Ctx : ∀ {ℓ} (Σ : Signature {ℓ}) (n : ℕ) → Set ℓ
Ctx Σ n = List (Fml Σ n)

infix 4 _∈ᶜ_
data _∈ᶜ_ {ℓ : Level} {A : Set ℓ} (x : A) : List A → Set ℓ where
  here  : ∀ {xs} → x ∈ᶜ (x ∷ xs)
  there : ∀ {y xs} → x ∈ᶜ xs → x ∈ᶜ (y ∷ xs)
