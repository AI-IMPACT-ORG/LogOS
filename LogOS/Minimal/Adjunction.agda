{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Adjunction where

open import LogOS.Prelude
open import LogOS.Minimal.Con
open import LogOS.Syntax.Prop as Prop using (_↔_)

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
    (c : ConPreorder.Con (BulkBoundary.bnd BB))
  → ConPreorder._⊑_ (BulkBoundary.bnd BB)
                 c
                 (LaxAdjunction.bnd LA (LaxAdjunction.ext LA c))
η LA c = LaxAdjunction.unit-lax LA c

ε
  : ∀ {ℓ} {BB : BulkBoundary ℓ}
    (LA : LaxAdjunction BB)
    (d : ConPreorder.Con (BulkBoundary.bulk BB))
  → ConPreorder._⊑_ (BulkBoundary.bulk BB)
                 (LaxAdjunction.ext LA (LaxAdjunction.bnd LA d))
                 d
ε LA d = LaxAdjunction.counit-lax LA d

-- Textbook-ish aliases: read `ext`/`bnd` as quantifier-like adjoints.
--
-- We avoid the literal `∀` identifier (Agda syntax), so we use `exists`/`forAll`.
-- These are just projections of the underlying `LaxAdjunction`; they add no
-- axioms and keep the original `ext`/`bnd` names as the primary API.

exists
  : ∀ {ℓ} {BB : BulkBoundary ℓ}
  → LaxAdjunction BB
  → BulkBoundary.Con_bnd BB
  → BulkBoundary.Con_bulk BB
exists LA = LaxAdjunction.ext LA

forAll
  : ∀ {ℓ} {BB : BulkBoundary ℓ}
  → LaxAdjunction BB
  → BulkBoundary.Con_bulk BB
  → BulkBoundary.Con_bnd BB
forAll LA = LaxAdjunction.bnd LA

-- Optional tensor/unit operations on (bulk, bnd), plus monotonicity.
--
-- Note: no associativity/unit laws are assumed here; those can be layered on
-- separately when needed.

record MonoidalOps {ℓ : Level} (CP : ConPreorder ℓ) : Set (lsuc ℓ) where
  infixl 7 _⊗_
  open ConPreorder CP
  field
    _⊗_   : Con → Con → Con
    I     : Con
    mono⊗ : ∀ {x x' y y'} → _⊑_ x x' → _⊑_ y y' → _⊑_ (_⊗_ x y) (_⊗_ x' y')

record LaxMonoidalAdjunction {ℓ : Level}
                             (BB : BulkBoundary ℓ)
                             (MBulk : MonoidalOps (BulkBoundary.bulk BB))
                             (MBnd  : MonoidalOps (BulkBoundary.bnd  BB))
                             : Set (lsuc ℓ) where
  -- Open only the derived names from BulkBoundary to avoid clashing with
  -- the adjunction’s bnd/ext fields (both named bnd/ext).
  open BulkBoundary BB using (Con_bulk; Con_bnd; _⊑bulk_; _⊑bnd_)
  open MonoidalOps MBulk renaming (_⊗_ to _⊗b_; I to Ib)
  open MonoidalOps MBnd  renaming (_⊗_ to _⊗∂_; I to I∂)
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

-- ============================================================================
-- Optional law layers (standard math strength)
-- ============================================================================

-- Monoidal laws for `MonoidalOps`, phrased as equality up to mutual refinement.
-- (Use this when you really want a monoid, not just “ops + monotonicity”.)

record MonoidalLaws {ℓ : Level}
                    {CP : ConPreorder ℓ}
                    (M : MonoidalOps CP) : Set (lsuc ℓ) where
  open ConPreorder CP
  open MonoidalOps M
  field
    ⊗-assoc : ∀ x y z → _≈CP_ CP ((x ⊗ y) ⊗ z) (x ⊗ (y ⊗ z))
    ⊗-idl   : ∀ x → _≈CP_ CP (I ⊗ x) x
    ⊗-idr   : ∀ x → _≈CP_ CP (x ⊗ I) x

-- Convenience bundle: ops + laws in one record.

record Monoidal {ℓ : Level} (CP : ConPreorder ℓ) : Set (lsuc ℓ) where
  field
    ops  : MonoidalOps CP
    laws : MonoidalLaws ops
  open MonoidalOps ops public
  open MonoidalLaws laws public

-- Antisymmetry upgrades the `≈`-level monoidal laws to equality-level laws.

module MonoidalLawsEq
  {ℓ : Level}
  {CP : ConPreorder ℓ}
  (po : PartialOrder CP)
  {ops : MonoidalOps CP}
  (laws : MonoidalLaws ops)
  where

  open ConPreorder CP
  open MonoidalOps ops
  open MonoidalLaws laws

  ⊗-assoc≡ : ∀ x y z → ((x ⊗ y) ⊗ z) ≡ (x ⊗ (y ⊗ z))
  ⊗-assoc≡ x y z = ≈CP→≡ po (⊗-assoc x y z)

  ⊗-idl≡ : ∀ x → (I ⊗ x) ≡ x
  ⊗-idl≡ x = ≈CP→≡ po (⊗-idl x)

  ⊗-idr≡ : ∀ x → (x ⊗ I) ≡ x
  ⊗-idr≡ x = ≈CP→≡ po (⊗-idr x)

-- A (tight) Galois connection / adjunction interface.
--
-- This is the standard “↔-law” form:
--   ext c ⊑ d    ↔    c ⊑ bnd d
--
-- From this, the library’s `LaxAdjunction` unit/counit inequalities are derived.

record GaloisConnection {ℓ : Level}
                        (BB : BulkBoundary ℓ) : Set (lsuc ℓ) where
  open BulkBoundary BB using (Con_bulk; Con_bnd; _⊑bulk_; _⊑bnd_)
  field
    ext : Con_bnd  → Con_bulk
    bnd : Con_bulk → Con_bnd
    adj : ∀ c d → _⊑bulk_ (ext c) d ↔ _⊑bnd_ c (bnd d)

  unit-lax : ∀ c → _⊑bnd_ c (bnd (ext c))
  unit-lax c =
    Prop._↔_.to (adj c (ext c))
      (ConPreorder.refl (BulkBoundary.bulk BB))

  counit-lax : ∀ d → _⊑bulk_ (ext (bnd d)) d
  counit-lax d =
    Prop._↔_.from (adj (bnd d) d)
      (ConPreorder.refl (BulkBoundary.bnd BB))

  ext-mono : ∀ {c c'} → _⊑bnd_ c c' → _⊑bulk_ (ext c) (ext c')
  ext-mono {c} {c'} c≤c' =
    Prop._↔_.from (adj c (ext c'))
      (ConPreorder.trans (BulkBoundary.bnd BB) c≤c' (unit-lax c'))

  bnd-mono : ∀ {d d'} → _⊑bulk_ d d' → _⊑bnd_ (bnd d) (bnd d')
  bnd-mono {d} {d'} d≤d' =
    Prop._↔_.to (adj (bnd d) d')
      (ConPreorder.trans (BulkBoundary.bulk BB) (counit-lax d) d≤d')

  laxAdjunction : LaxAdjunction BB
  laxAdjunction =
    record
      { ext = ext
      ; bnd = bnd
      ; unit-lax = unit-lax
      ; counit-lax = counit-lax
      }

-- Optional strengthening: a monotone `LaxAdjunction` already determines a
-- (tight) `GaloisConnection`.
--
-- The core interface keeps monotonicity out of `LaxAdjunction` because several
-- applications only need unit/counit inequalities. When you *do* have
-- monotonicity for `ext` and `bnd`, the ↔-law follows.

record LaxAdjunctionMono {ℓ : Level}
                         (BB : BulkBoundary ℓ) : Set (lsuc ℓ) where
  open BulkBoundary BB using (Con_bulk; Con_bnd; _⊑bulk_; _⊑bnd_)
  field
    core : LaxAdjunction BB
  open LaxAdjunction core public
  field
    ext-mono : ∀ {c c'} → _⊑bnd_ c c' → _⊑bulk_ (ext c) (ext c')
    bnd-mono : ∀ {d d'} → _⊑bulk_ d d' → _⊑bnd_ (bnd d) (bnd d')

  adj
    : ∀ c d
    → _⊑bulk_ (ext c) d ↔ _⊑bnd_ c (bnd d)
  adj c d =
    Prop.intro
      (λ extc≤d →
        ConPreorder.trans (BulkBoundary.bnd BB)
          (unit-lax c)
          (bnd-mono extc≤d))
      (λ c≤bndd →
        ConPreorder.trans (BulkBoundary.bulk BB)
          (ext-mono c≤bndd)
          (counit-lax d))

  galoisConnection : GaloisConnection BB
  galoisConnection =
    record
      { ext = ext
      ; bnd = bnd
      ; adj = adj
      }

-- Optional strengthening: bundle monotonicity for a lax monoidal adjunction.
--
-- This mirrors `LaxAdjunctionMono`, but keeps the monoidal laxity data available.

record LaxMonoidalAdjunctionMono {ℓ : Level}
                                 (BB : BulkBoundary ℓ)
                                 (MBulk : MonoidalOps (BulkBoundary.bulk BB))
                                 (MBnd  : MonoidalOps (BulkBoundary.bnd  BB))
                                 : Set (lsuc ℓ) where
  open BulkBoundary BB using (Con_bulk; Con_bnd; _⊑bulk_; _⊑bnd_)
  field
    core : LaxMonoidalAdjunction BB MBulk MBnd

  open LaxMonoidalAdjunction core public renaming (core to coreAdj)

  field
    ext-mono : ∀ {c c'} → _⊑bnd_ c c' → _⊑bulk_ (ext c) (ext c')
    bnd-mono : ∀ {d d'} → _⊑bulk_ d d' → _⊑bnd_ (bnd d) (bnd d')

  laxAdjunctionMono : LaxAdjunctionMono BB
  laxAdjunctionMono =
    record
      { core = coreAdj
      ; ext-mono = ext-mono
      ; bnd-mono = bnd-mono
      }

  galoisConnection : GaloisConnection BB
  galoisConnection = LaxAdjunctionMono.galoisConnection laxAdjunctionMono
