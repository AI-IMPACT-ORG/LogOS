{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.CategoryTheory.AdjunctionMonads where

-- Very general derived structure from an order-enriched (lax) adjunction:
-- once `ext` and `bnd` are monotone, unit/counit inequalities induce
--   - a boundary closure operator  T = bnd ∘ ext   (monad on the preorder), and
--   - a bulk interior operator     S = ext ∘ bnd   (comonad on the preorder).

open import LogOS.Prelude

open import LogOS.Minimal.Adjunction using (LaxAdjunction; LaxMonoidalAdjunction; MonoidalPoset)
open import LogOS.Minimal.Con using (ConPoset; BulkBoundary; MonoMap)

open import LogOS.Syntax.Prop as Prop
open import LogOS.Theorems.Reflection.Projector using (Projector; Coreflector)
open import LogOS.Theorems.Modal.S4 using (S4Modality)

module Derived
  {ℓ : Level}
  {BB : BulkBoundary ℓ}
  (LA : LaxAdjunction BB)
  (mono-ext : MonoMap (BulkBoundary.bnd BB) (BulkBoundary.bulk BB) (LaxAdjunction.ext LA))
  (mono-bnd : MonoMap (BulkBoundary.bulk BB) (BulkBoundary.bnd BB) (LaxAdjunction.bnd LA))
  where

  open BulkBoundary BB using (Con_bulk; Con_bnd; _⊑bulk_; _⊑bnd_)
  open LaxAdjunction LA

  -- Derived Galois connection (adjunction) law.
  --
  -- This is the order-enriched “adjunction iff”:
  --   ext c ⊑ d    ↔    c ⊑ bnd d
  --
  -- It is forced by unit/counit once monotonicity is available.

  adj
    : ∀ (c : Con_bnd) (d : Con_bulk)
    → (_⊑bulk_ (ext c) d → _⊑bnd_ c (bnd d))
      × (_⊑bnd_ c (bnd d) → _⊑bulk_ (ext c) d)
  adj c d =
    let
      to : _⊑bulk_ (ext c) d → _⊑bnd_ c (bnd d)
      to ext≤ =
        ConPoset.trans (BulkBoundary.bnd BB)
          (unit-lax c)
          (mono-bnd ext≤)

      from : _⊑bnd_ c (bnd d) → _⊑bulk_ (ext c) d
      from c≤ =
        ConPoset.trans (BulkBoundary.bulk BB)
          (mono-ext c≤)
          (counit-lax d)
    in
    (to , from)

  -- Same law packaged as a LogOS-style bi-implication (`_↔_`).

  adj↔
    : ∀ (c : Con_bnd) (d : Con_bulk)
    → Prop._↔_ (_⊑bulk_ (ext c) d) (_⊑bnd_ c (bnd d))
  adj↔ c d =
    Prop.intro
      (λ ext≤ → fst (adj c d) ext≤)
      (λ c≤ → snd (adj c d) c≤)

  -- Boundary closure operator (monad on the preorder).

  T : Con_bnd → Con_bnd
  T c = bnd (ext c)

  T-mono : MonoMap (BulkBoundary.bnd BB) (BulkBoundary.bnd BB) T
  T-mono le = mono-bnd (mono-ext le)

  T-unit : ∀ c → _⊑bnd_ c (T c)
  T-unit = unit-lax

  -- “Multiplication” (idempotent-lax): T (T c) ⊑ T c.
  T-mult-lax : ∀ c → _⊑bnd_ (T (T c)) (T c)
  T-mult-lax c =
    mono-bnd (counit-lax (ext c))

  -- The other direction is derivable from monotonicity + unit.
  T-mult-infl : ∀ c → _⊑bnd_ (T c) (T (T c))
  T-mult-infl c = T-mono (T-unit c)

  -- Bulk interior operator (comonad on the preorder).

  S : Con_bulk → Con_bulk
  S d = ext (bnd d)

  S-mono : MonoMap (BulkBoundary.bulk BB) (BulkBoundary.bulk BB) S
  S-mono le = mono-ext (mono-bnd le)

  S-counit : ∀ d → _⊑bulk_ (S d) d
  S-counit = counit-lax

  -- “Comultiplication” (idempotent-lax for a comonad): S d ⊑ S (S d).
  S-comult-lax : ∀ d → _⊑bulk_ (S d) (S (S d))
  S-comult-lax d =
    let
      bd≤ : _⊑bnd_ (bnd d) (bnd (ext (bnd d)))
      bd≤ = unit-lax (bnd d)
    in mono-ext bd≤

  -- The other direction is derivable from monotonicity + counit.
  S-comult-counit : ∀ d → _⊑bulk_ (S (S d)) (S d)
  S-comult-counit d = S-mono (S-counit d)

  -- Boundary closure as a shared projector instance.

  T-projector : Projector (BulkBoundary.bnd BB)
  T-projector = record
    { P = T
    ; infl = T-unit
    ; idemp-lax = T-mult-lax
    }

  -- Same structure as an S4 modality (monotone + inflationary + idempotent-lax).

  T-modality : S4Modality (BulkBoundary.bnd BB)
  T-modality = record
    { □ = T
    ; mono = T-mono
    ; infl = T-unit
    ; idemp-lax = T-mult-lax
    }

  -- Bulk interior as a shared coreflector instance.

  S-coreflector : Coreflector (BulkBoundary.bulk BB)
  S-coreflector = record
    { I = S
    ; defl = S-counit
    ; idemp-lax = S-comult-counit
    }

  -- -------------------------------------------------------------------------
  -- Lax holography: stable boundary theories ↔ stable bulk theories.
  -- -------------------------------------------------------------------------
  --
  -- From the lax adjunction, we obtain:
  --   T = bnd ∘ ext  (boundary closure; always c ⊑ T c)
  --   S = ext ∘ bnd  (bulk interior; always S d ⊑ d)
  --
  -- The “stable” fragments are the fixed points up to refinement:
  --   StableBnd  = { c | T c ⊑ c }
  --   StableBulk = { d | d ⊑ S d }
  --
  -- On these fragments, `ext` and `bnd` form an order isomorphism (up to the
  -- ambient preorders, without antisymmetry).

  module LaxHolography where

    StableBnd : Set ℓ
    StableBnd = Σ Con_bnd (λ c → _⊑bnd_ (T c) c)

    StableBulk : Set ℓ
    StableBulk = Σ Con_bulk (λ d → _⊑bulk_ d (S d))

    toBnd : StableBnd → Con_bnd
    toBnd = proj₁

    stableBnd : (x : StableBnd) → _⊑bnd_ (T (toBnd x)) (toBnd x)
    stableBnd = proj₂

    toBulk : StableBulk → Con_bulk
    toBulk = proj₁

    stableBulk : (x : StableBulk) → _⊑bulk_ (toBulk x) (S (toBulk x))
    stableBulk = proj₂

    -- Induced preorders (inherit order from the ambient ones via projection).

    infix 4 _≤∂_ _≤b_

    _≤∂_ : StableBnd → StableBnd → Set ℓ
    x ≤∂ y = _⊑bnd_ (toBnd x) (toBnd y)

    _≤b_ : StableBulk → StableBulk → Set ℓ
    x ≤b y = _⊑bulk_ (toBulk x) (toBulk y)

    StableBndPoset : ConPoset ℓ
    StableBndPoset = record
      { Con = StableBnd
      ; _⊑_ = _≤∂_
      ; refl = λ {x} → ConPoset.refl (BulkBoundary.bnd BB) {c = toBnd x}
      ; trans = λ {x} {y} {z} xy yz → ConPoset.trans (BulkBoundary.bnd BB) xy yz
      }

    StableBulkPoset : ConPoset ℓ
    StableBulkPoset = record
      { Con = StableBulk
      ; _⊑_ = _≤b_
      ; refl = λ {x} → ConPoset.refl (BulkBoundary.bulk BB) {c = toBulk x}
      ; trans = λ {x} {y} {z} xy yz → ConPoset.trans (BulkBoundary.bulk BB) xy yz
      }

    -- Restricted maps: ext lands in the stable bulk fragment, bnd lands in the
    -- stable boundary fragment.

    extStable : StableBnd → StableBulk
    extStable x =
      ( ext (toBnd x)
      , mono-ext (unit-lax (toBnd x))
      )

    bndStable : StableBulk → StableBnd
    bndStable x =
      ( bnd (toBulk x)
      , mono-bnd (counit-lax (toBulk x))
      )

    -- Monotonicity of the restricted maps.

    extStable-mono : MonoMap StableBndPoset StableBulkPoset extStable
    extStable-mono le = mono-ext le

    bndStable-mono : MonoMap StableBulkPoset StableBndPoset bndStable
    bndStable-mono le = mono-bnd le

    -- Inverse laws on stable fragments (up to refinement in the ambient posets).

    bndStable∘extStable≤ : ∀ x → bndStable (extStable x) ≤∂ x
    bndStable∘extStable≤ x = stableBnd x

    bndStable∘extStable≥ : ∀ x → x ≤∂ bndStable (extStable x)
    bndStable∘extStable≥ x = unit-lax (toBnd x)

    extStable∘bndStable≤ : ∀ x → extStable (bndStable x) ≤b x
    extStable∘bndStable≤ x = counit-lax (toBulk x)

    extStable∘bndStable≥ : ∀ x → x ≤b extStable (bndStable x)
    extStable∘bndStable≥ x = stableBulk x

    -- Order reflection (hence order isomorphism structure) on stable fragments.

    extStable-reflects : ∀ {x y} → extStable x ≤b extStable y → x ≤∂ y
    extStable-reflects {x} {y} ext≤ =
      let
        c = toBnd x
        d = toBnd y
        c≤Td : _⊑bnd_ c (T d)
        c≤Td = fst (adj c (ext d)) ext≤
      in
      ConPoset.trans (BulkBoundary.bnd BB) c≤Td (stableBnd y)

    bndStable-reflects : ∀ {x y} → bndStable x ≤∂ bndStable y → x ≤b y
    bndStable-reflects {x} {y} bnd≤ =
      let
        d = toBulk x
        e = toBulk y
        d≤Sd : _⊑bulk_ d (S d)
        d≤Sd = stableBulk x
        Sd≤Se : _⊑bulk_ (S d) (S e)
        Sd≤Se = mono-ext bnd≤
        Se≤e : _⊑bulk_ (S e) e
        Se≤e = counit-lax e
      in
      ConPoset.trans (BulkBoundary.bulk BB) d≤Sd
        (ConPoset.trans (BulkBoundary.bulk BB) Sd≤Se Se≤e)

module DerivedMonoidal
  {ℓ : Level}
  {BB : BulkBoundary ℓ}
  {MBulk : MonoidalPoset (BulkBoundary.bulk BB)}
  {MBnd  : MonoidalPoset (BulkBoundary.bnd  BB)}
  (Holo : LaxMonoidalAdjunction BB MBulk MBnd)
  (mono-ext : MonoMap (BulkBoundary.bnd BB) (BulkBoundary.bulk BB) (LaxMonoidalAdjunction.ext Holo))
  (mono-bnd : MonoMap (BulkBoundary.bulk BB) (BulkBoundary.bnd BB) (LaxMonoidalAdjunction.bnd Holo))
  where

  open BulkBoundary BB using (Con_bulk; Con_bnd; _⊑bulk_; _⊑bnd_)
  open MonoidalPoset MBulk renaming (_⊗_ to _⊗b_; I to Ib)
  open MonoidalPoset MBnd  renaming (_⊗_ to _⊗∂_; I to I∂)
  open LaxMonoidalAdjunction Holo

  module Base = Derived (core) mono-ext mono-bnd
  open Base using (T; S)

  -- The induced boundary closure operator is lax monoidal.

  T-⊗-lax : ∀ x y → _⊑bnd_ (T (x ⊗∂ y)) (T x ⊗∂ T y)
  T-⊗-lax x y =
    ConPoset.trans (BulkBoundary.bnd BB)
      (mono-bnd (ext-⊗-lax x y))
      (bnd-⊗-lax (ext x) (ext y))

  T-I-lax : _⊑bnd_ (T I∂) I∂
  T-I-lax =
    ConPoset.trans (BulkBoundary.bnd BB)
      (mono-bnd ext-I-lax)
      bnd-I-lax

  -- The induced bulk interior operator is lax monoidal.

  S-⊗-lax : ∀ x y → _⊑bulk_ (S (x ⊗b y)) (S x ⊗b S y)
  S-⊗-lax x y =
    ConPoset.trans (BulkBoundary.bulk BB)
      (mono-ext (bnd-⊗-lax x y))
      (ext-⊗-lax (bnd x) (bnd y))

  S-I-lax : _⊑bulk_ (S Ib) Ib
  S-I-lax =
    ConPoset.trans (BulkBoundary.bulk BB)
      (mono-ext bnd-I-lax)
      ext-I-lax
