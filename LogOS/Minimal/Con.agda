{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Con where

open import Level using (Level; lsuc)
open import Data.Relation.Binary.PropositionalEquality using (_≡_)

-- Minimal constraint carriers with preorder

record ConPoset (ℓ : Level) : Set (lsuc ℓ) where
  infix 4 _⊑_
  field
    Con  : Set ℓ
    _⊑_  : Con → Con → Set ℓ
    refl : ∀ {c} → _⊑_ c c
    trans : ∀ {a b c} → _⊑_ a b → _⊑_ b c → _⊑_ a c

-- Monotonicity of an endomap on a constraint poset.

MonoOn : ∀ {ℓ} (CP : ConPoset ℓ) → (ConPoset.Con CP → ConPoset.Con CP) → Set ℓ
MonoOn CP f = ∀ {c d} → ConPoset._⊑_ CP c d → ConPoset._⊑_ CP (f c) (f d)

-- Optionally distinguish bulk/boundary posets

record BulkBoundary (ℓ : Level) : Set (lsuc ℓ) where
  field
    bulk : ConPoset ℓ
    bnd  : ConPoset ℓ

  open ConPoset bulk public renaming (Con to Con_bulk; _⊑_ to _⊑bulk_)
  open ConPoset bnd  public renaming (Con to Con_bnd;  _⊑_ to _⊑bnd_)

-- Optional strengthening to partial orders (add antisymmetry)

record PartialOrder {ℓ : Level} (CP : ConPoset ℓ) : Set (lsuc ℓ) where
  open ConPoset CP
  field
    antisym : ∀ {a b} → _⊑_ a b → _⊑_ b a → a ≡ b

record BulkBoundaryPO {ℓ : Level} (BB : BulkBoundary ℓ) : Set (lsuc ℓ) where
  open BulkBoundary BB
  field
    po-bulk : PartialOrder bulk
    po-bnd  : PartialOrder bnd
