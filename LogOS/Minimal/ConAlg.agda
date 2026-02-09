{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.ConAlg where

open import LogOS.Prelude
open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Prelude using (_≡_; refl; trans; cong; cong₂)

-- Constraint algebra: bulk/boundary preorders + monoids + lax monoidal adjunction

record ConAlg {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
  field
    BB    : BulkBoundary ℓ
    MBulk : MonoidalOps (BulkBoundary.bulk BB)
    MBnd  : MonoidalOps (BulkBoundary.bnd  BB)
    Holo  : LaxMonoidalAdjunction BB MBulk MBnd

  open BulkBoundary BB public
  open MonoidalOps MBulk public renaming (_⊗_ to _⊗b_; I to Ib)
  open MonoidalOps MBnd  public renaming (_⊗_ to _⊗∂_; I to I∂)
  open LaxMonoidalAdjunction Holo public

-- Core map between constraint algebras (carrier map + monotonicity only).
--
-- Note: this does not by itself assert unit/tensor/adjunction preservation.
-- Those laws live in `ConAlgHomLaws`.

record ConAlgHom {ℓ : Level} (A B : ConAlg {ℓ}) : Set (lsuc ℓ) where
  open ConAlg A renaming (Con_bnd to Con_bndA; Con_bulk to Con_bulkA; _⊑bnd_ to ≤∂A; _⊑bulk_ to ≤bA;
                          _⊗b_ to _⊗bA_; _⊗∂_ to _⊗∂A_; Ib to IbA; I∂ to I∂A; ext to extA; Holo to HoloA)
  open ConAlg B renaming (Con_bnd to Con_bndB; Con_bulk to Con_bulkB; _⊑bnd_ to ≤∂B; _⊑bulk_ to ≤bB;
                          _⊗b_ to _⊗bB_; _⊗∂_ to _⊗∂B_; Ib to IbB; I∂ to I∂B; ext to extB; Holo to HoloB)
  field
    map∂ : Con_bndA → Con_bndB
    mapb : Con_bulkA → Con_bulkB

    mono∂ : ∀ {x y} → ≤∂A x y → ≤∂B (map∂ x) (map∂ y)
    monob : ∀ {x y} → ≤bA  x y → ≤bB  (mapb x) (mapb y)

ConAlgMap : ∀ {ℓ : Level} → ConAlg {ℓ} → ConAlg {ℓ} → Set (lsuc ℓ)
ConAlgMap = ConAlgHom

-- Optional law layer for `ConAlgHom` (lax, preorder-directed preservation).
record ConAlgHomLaws {ℓ : Level} {A B : ConAlg {ℓ}} (f : ConAlgHom A B) : Set (lsuc ℓ) where
  open ConAlg A renaming (Con_bnd to Con_bndA; Con_bulk to Con_bulkA; _⊑bnd_ to ≤∂A; _⊑bulk_ to ≤bA;
                          _⊗b_ to _⊗bA_; _⊗∂_ to _⊗∂A_; Ib to IbA; I∂ to I∂A; ext to extA; Holo to HoloA)
  open ConAlg B renaming (Con_bnd to Con_bndB; Con_bulk to Con_bulkB; _⊑bnd_ to ≤∂B; _⊑bulk_ to ≤bB;
                          _⊗b_ to _⊗bB_; _⊗∂_ to _⊗∂B_; Ib to IbB; I∂ to I∂B; ext to extB; Holo to HoloB)
  open ConAlgHom f
  field
    unit∂-lax : ≤∂B (map∂ I∂A) I∂B
    unitb-lax : ≤bB (mapb IbA) IbB
    ten∂-lax  : ∀ x y → ≤∂B (map∂ (_⊗∂A_ x y)) (_⊗∂B_ (map∂ x) (map∂ y))
    tenb-lax  : ∀ x y → ≤bB (mapb (_⊗bA_ x y)) (_⊗bB_ (mapb x) (mapb y))
    ext-comm-lax : ∀ c → ≤bB (mapb (extA c)) (extB (map∂ c))
    bnd-comm-lax : ∀ d
      → ≤∂B (map∂ (LaxMonoidalAdjunction.bnd HoloA d))
            (LaxMonoidalAdjunction.bnd HoloB (mapb d))

-- Bundled variant when a law-carrying map is required.
record ConAlgHomWithLaws {ℓ : Level} (A B : ConAlg {ℓ}) : Set (lsuc ℓ) where
  field
    core : ConAlgHom A B
    laws : ConAlgHomLaws core

-- Pointwise comparison of core maps (enriched uniqueness notion).

record ConAlgHomLe {ℓ : Level} {A B : ConAlg {ℓ}} (f g : ConAlgHom A B) : Set (lsuc ℓ) where
  open ConAlgHom f renaming (map∂ to f∂; mapb to fb)
  open ConAlgHom g renaming (map∂ to g∂; mapb to gb)
  open ConAlg B
  field
    le∂ : ∀ x → _⊑bnd_ (f∂ x) (g∂ x)
    leb : ∀ d → _⊑bulk_ (fb  d) (gb  d)

-- Strict homomorphism (on-the-nose preservation for initiality proof)


record ConAlgHom≡ {ℓ : Level} (A B : ConAlg {ℓ}) : Set (lsuc ℓ) where
  open ConAlg A renaming (Con_bnd to Con_bndA; Con_bulk to Con_bulkA; _⊗b_ to _⊗bA_; _⊗∂_ to _⊗∂A_; Ib to IbA; I∂ to I∂A; ext to extA; Holo to HoloA)
  open ConAlg B renaming (Con_bnd to Con_bndB; Con_bulk to Con_bulkB; _⊗b_ to _⊗bB_; _⊗∂_ to _⊗∂B_; Ib to IbB; I∂ to I∂B; ext to extB; Holo to HoloB)
  field
    map∂ : Con_bndA → Con_bndB
    mapb : Con_bulkA → Con_bulkB
    unit∂ : map∂ I∂A ≡ I∂B
    unitb : mapb IbA  ≡ IbB
    ten∂  : ∀ x y → map∂ (_⊗∂A_ x y) ≡ _⊗∂B_ (map∂ x) (map∂ y)
    tenb  : ∀ x y → mapb (_⊗bA_ x y)  ≡ _⊗bB_ (mapb x) (mapb y)
    ext-comm : ∀ c → mapb (extA c) ≡ extB (map∂ c)
    bnd-comm : ∀ d → map∂ (LaxMonoidalAdjunction.bnd HoloA d) ≡ LaxMonoidalAdjunction.bnd HoloB (mapb d)

-- Identity and composition for strict homs

idHom≡ : ∀ {ℓ} (A : ConAlg {ℓ}) → ConAlgHom≡ A A
idHom≡ A = record
  { map∂ = λ x → x
  ; mapb = λ d → d
  ; unit∂ = refl
  ; unitb = refl
  ; ten∂  = λ _ _ → refl
  ; tenb  = λ _ _ → refl
  ; ext-comm = λ _ → refl
  ; bnd-comm = λ _ → refl
  }

composeHom≡ : ∀ {ℓ} {A B C : ConAlg {ℓ}}
             → ConAlgHom≡ A B → ConAlgHom≡ B C → ConAlgHom≡ A C
composeHom≡ f g = record
  { map∂ = λ x → ConAlgHom≡.map∂ g (ConAlgHom≡.map∂ f x)
  ; mapb = λ d → ConAlgHom≡.mapb g (ConAlgHom≡.mapb f d)
  ; unit∂ = trans (cong (ConAlgHom≡.map∂ g) (ConAlgHom≡.unit∂ f)) (ConAlgHom≡.unit∂ g)
  ; unitb = trans (cong (ConAlgHom≡.mapb g) (ConAlgHom≡.unitb f)) (ConAlgHom≡.unitb g)
  ; ten∂  = λ x y → trans (cong (ConAlgHom≡.map∂ g) (ConAlgHom≡.ten∂ f x y))
                          (ConAlgHom≡.ten∂ g _ _)
  ; tenb  = λ x y → trans (cong (ConAlgHom≡.mapb g) (ConAlgHom≡.tenb f x y))
                          (ConAlgHom≡.tenb g _ _)
  ; ext-comm = λ c → trans (cong (ConAlgHom≡.mapb g) (ConAlgHom≡.ext-comm f c)) (ConAlgHom≡.ext-comm g _)
  ; bnd-comm = λ d → trans (cong (ConAlgHom≡.map∂ g) (ConAlgHom≡.bnd-comm f d)) (ConAlgHom≡.bnd-comm g _)
  }
