{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Host.Product where

open import LogOS.Host.Level using (Level; _⊔_)

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
-- Non-dependent product (pair type) as a proper record.
infixr 2 _×_

record _×_ {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public
