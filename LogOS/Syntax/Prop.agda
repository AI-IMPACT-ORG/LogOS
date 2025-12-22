{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Syntax.Prop where

-- ============================================================================
-- PROPOSITIONAL CONNECTIVES
-- Logical connectives for propositional logic
-- ============================================================================
--
-- This module defines lightweight propositional connectives used throughout the
-- library for coherence and observational equality (notably `_↔_`).
--
-- The minimal truth layer continues to use Agda equality `_≡_` where appropriate;
-- `_↔_` is used to state logical equivalence without assuming function extensionality.
-- ============================================================================

-- Equality conventions (guidance)
-- - Use `_≡_` for meta-level propositional equality in Agda.
-- - Use `_↔_` for logical equivalence/coherence (pairs of functions).
-- - For decode-level equality tied to a specific kernel, prefer opening
--   `LogOS.Syntax.Eq.ForKernel K` and use `_≃K_` for `decode γ₁ ≡ decode γ₂`.

open import LogOS.Prelude
open import Data.Product using (_×_)

-- Logical equivalence (bi-implication)
infix 3 _↔_
record _↔_ {ℓ : Level} (P Q : Set ℓ) : Set ℓ where
  constructor intro
  field
    to : P → Q
    from : Q → P

open _↔_ public

-- Conjunction (already available as _×_, but provided for logical clarity)
infixr 4 _∧_
_∧_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
P ∧ Q = P × Q

-- Disjunction (sum type)
infixr 3 _∨_
_∨_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
_∨_ {ℓ} P Q = P ⊎ Q
  where
    open import Data.Sum using (_⊎_)

-- Truth (unit type): `⊤` is available via `LogOS.Prelude`.

-- Falsity (empty type)
data ⊥ {ℓ : Level} : Set ℓ where

⊥-elim : ∀ {ℓ₁ ℓ₂ : Level} {A : Set ℓ₂} → ⊥ {ℓ₁} → A
⊥-elim ()

-- Negation
infix 6 ¬_
¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬_ {ℓ} P = P → ⊥ {lzero}
