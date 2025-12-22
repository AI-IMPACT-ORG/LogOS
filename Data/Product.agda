{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Data.Product where

open import Level using (Level; _⊔_)
open import Data.Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Minimal dependent pair type Σ, mirroring std-lib's Data.Product.
-- Defined as a record so proj₂ is definitional (no postulate needed).

infixr 4 Σ
infixr 5 _,_

record Σ {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

-- Non-dependent product (pair type) as a proper record
-- This is the natural binary product type that the logic already knows
infixr 2 _×_

record _×_ {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public
