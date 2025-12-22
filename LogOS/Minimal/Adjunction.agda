{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Adjunction where

open import LogOS.Prelude
open import LogOS.Minimal.Con

-- Lax adjunction between boundary and bulk constraints

record LaxAdjunction {ℓ : Level}
                     (BB : BulkBoundary ℓ)
                     : Set (lsuc ℓ) where
  open BulkBoundary BB
  field
    ext : Con_bnd  → Con_bulk
    bnd : Con_bulk → Con_bnd

    -- Lax unit/counit
    -- Axiom: unit-lax  c ≤ bnd (ext c)
    unit-lax   : ∀ (c : Con_bnd)  → _⊑bnd_ c (bnd (ext c))
    -- Axiom: counit-lax ext (bnd d) ≤ d
    counit-lax : ∀ (d : Con_bulk) → _⊑bulk_ (ext (bnd d)) d

-- Aliases (η, ε) to make unit/counit shape explicit when using a LaxAdjunction
-- These are just thin wrappers; they do not add axioms.

η
  : ∀ {ℓ} {BB : BulkBoundary ℓ}
    (LA : LaxAdjunction BB)
    (c : ConPoset.Con (BulkBoundary.bnd BB))
  → ConPoset._⊑_ (BulkBoundary.bnd BB)
                 c
                 (LaxAdjunction.bnd LA (LaxAdjunction.ext LA c))
η LA c = LaxAdjunction.unit-lax LA c

ε
  : ∀ {ℓ} {BB : BulkBoundary ℓ}
    (LA : LaxAdjunction BB)
    (d : ConPoset.Con (BulkBoundary.bulk BB))
  → ConPoset._⊑_ (BulkBoundary.bulk BB)
                 (LaxAdjunction.ext LA (LaxAdjunction.bnd LA d))
                 d
ε LA d = LaxAdjunction.counit-lax LA d

-- Optional monoidal structure on (bulk, bnd) and lax monoidality of ext/bnd

record MonoidalPoset {ℓ : Level} (CP : ConPoset ℓ) : Set (lsuc ℓ) where
  infixl 7 _⊗_
  open ConPoset CP
  field
    _⊗_   : Con → Con → Con
    I     : Con
    mono⊗ : ∀ {x x' y y'} → _⊑_ x x' → _⊑_ y y' → _⊑_ (_⊗_ x y) (_⊗_ x' y')

record LaxMonoidalAdjunction {ℓ : Level}
                             (BB : BulkBoundary ℓ)
                             (MBulk : MonoidalPoset (BulkBoundary.bulk BB))
                             (MBnd  : MonoidalPoset (BulkBoundary.bnd  BB))
                             : Set (lsuc ℓ) where
  -- Open only the derived names from BulkBoundary to avoid clashing with
  -- the adjunction’s bnd/ext fields (both named bnd/ext).
  open BulkBoundary BB using (Con_bulk; Con_bnd; _⊑bulk_; _⊑bnd_)
  open MonoidalPoset MBulk renaming (_⊗_ to _⊗b_; I to Ib)
  open MonoidalPoset MBnd  renaming (_⊗_ to _⊗∂_; I to I∂)
  field
    core : LaxAdjunction BB
  open LaxAdjunction core public
  field
    -- Axiom: ext monoidal laxity ext(x ⊗∂ y) ≤ ext x ⊗b ext y; ext I∂ ≤ Ib
    ext-⊗-lax : ∀ x y → _⊑bulk_ (ext (x ⊗∂ y)) (ext x ⊗b ext y)
    ext-I-lax : _⊑bulk_ (ext I∂) Ib
    -- Axiom: bnd monoidal laxity bnd(x ⊗b y) ≤ bnd x ⊗∂ bnd y; bnd Ib ≤ I∂
    bnd-⊗-lax : ∀ x y → _⊑bnd_ (bnd (x ⊗b y)) (bnd x ⊗∂ bnd y)
    bnd-I-lax : _⊑bnd_ (bnd Ib) I∂
