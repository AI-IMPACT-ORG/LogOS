{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Constraints where

open import LogOS.Prelude
open import LogOS.Prelude using (_×_; _,_)
open import LogOS.Prelude as Eq using (refl; trans; cong; cong₂)
open import LogOS.Syntax.Prop using (⊥)

open import LogOS.Minimal.Con
open import LogOS.Minimal.Adjunction
open import LogOS.Minimal.ConAlg
open import LogOS.Minimal.ConstraintsIndexed as Core

-- ============================================================================
-- Free constraint algebra with two sorts (boundary, bulk).
--
-- This is a specialisation of the indexed core (`ConstraintsIndexed`) with:
-- - a single dummy index `⊤`, and
-- - no atomic generators (`Atom = ⊥`).
--
-- The public API matches the historical `LogOS.Free.Constraints` module.
-- ============================================================================

private
  Idx₀ : Set lzero
  Idx₀ = ⊤ {ℓ = lzero}

  ⋆ : Idx₀
  ⋆ = tt

  module C {ℓ : Level} =
    Core.With {ι = lzero} {ℓ = ℓ}
      Idx₀
      (λ _ → ⊥ {ℓ = ℓ})

Con∂ : ∀ {ℓ : Level} → Set ℓ
Con∂ {ℓ} = C.Con∂ {ℓ = ℓ} ⋆

Conb : ∀ {ℓ : Level} → Set ℓ
Conb {ℓ} = C.Conb {ℓ = ℓ} ⋆

_≤∂_ : ∀ {ℓ : Level} → Con∂ {ℓ} → Con∂ {ℓ} → Set ℓ
_≤∂_ {ℓ} = C._≤∂_ {ℓ = ℓ} {i = ⋆}

_≤b_ : ∀ {ℓ : Level} → Conb {ℓ} → Conb {ℓ} → Set ℓ
_≤b_ {ℓ} = C._≤b_ {ℓ = ℓ} {i = ⋆}

infix 4 _≤∂_ _≤b_

-- Re-export the constructors and preorder rules (but not the impossible atom constructor).

module _ {ℓ : Level} where
  open C {ℓ = ℓ} public using
    ( I∂; _⊗∂_; bnd
    ; Ib; _⊗b_; ext
    ; refl∂; trans∂; cong⊗∂; unitbnd; bnd-⊗; bnd-I
    ; reflb; transb; cong⊗b; counit; ext-⊗; ext-I
    )

-- Build ConPreorder/Monoidal/LaxAdjunction from syntax

conPreorder∂ : ∀ {ℓ} → ConPreorder ℓ
conPreorder∂ {ℓ} = C.conPreorder∂ {ℓ = ℓ} ⋆

conPreorderb : ∀ {ℓ} → ConPreorder ℓ
conPreorderb {ℓ} = C.conPreorderb {ℓ = ℓ} ⋆

BBfree : ∀ {ℓ} → BulkBoundary ℓ
BBfree {ℓ} = C.BBfree {ℓ = ℓ} ⋆

MBulkfree : ∀ {ℓ} → MonoidalOps (BulkBoundary.bulk (BBfree {ℓ}))
MBulkfree {ℓ} = C.MBulkfree {ℓ = ℓ} ⋆

MBndfree : ∀ {ℓ} → MonoidalOps (BulkBoundary.bnd (BBfree {ℓ}))
MBndfree {ℓ} = C.MBndfree {ℓ = ℓ} ⋆

Holofree : ∀ {ℓ} → LaxMonoidalAdjunction (BBfree {ℓ}) (MBulkfree {ℓ}) (MBndfree {ℓ})
Holofree {ℓ} = C.Holofree {ℓ = ℓ} ⋆

FreeConAlg : ∀ {ℓ} → ConAlg {ℓ}
FreeConAlg {ℓ} = C.FreeConAlg {ℓ = ℓ} ⋆

-- Initiality: unique hom from FreeConAlg to any ConAlg, up to pointwise ≤

interp∂ : ∀ {ℓ} (A : ConAlg {ℓ}) → Con∂ {ℓ} → ConAlg.Con_bnd A
interp∂ {ℓ} A = C.interp∂ {ℓ = ℓ} ⋆ A (λ ())

interpb : ∀ {ℓ} (A : ConAlg {ℓ}) → Conb {ℓ} → ConAlg.Con_bulk A
interpb {ℓ} A = C.interpb {ℓ = ℓ} ⋆ A (λ ())

-- Monotonicity of interpretation

interp∂-mono
  : ∀ {ℓ} (A : ConAlg {ℓ}) {x y}
  → x ≤∂ y
  → ConAlg._⊑bnd_ A (interp∂ A x) (interp∂ A y)
interp∂-mono {ℓ} A = C.interp∂-mono {ℓ = ℓ} ⋆ A (λ ())

interpb-mono
  : ∀ {ℓ} (A : ConAlg {ℓ}) {x y}
  → x ≤b y
  → ConAlg._⊑bulk_ A (interpb A x) (interpb A y)
interpb-mono {ℓ} A = C.interpb-mono {ℓ = ℓ} ⋆ A (λ ())

-- Build the universal hom Free → A

to : ∀ {ℓ} (A : ConAlg {ℓ}) → ConAlgHom FreeConAlg A
to A = record
  { map∂ = interp∂ A
  ; mapb = interpb A
  ; mono∂ = interp∂-mono A
  ; monob = interpb-mono A
  }

-- Strict fold: structure-preserving on-the-nose (for uniqueness)

fold≡ : ∀ {ℓ} (A : ConAlg {ℓ}) → ConAlgHom≡ FreeConAlg A
fold≡ A = record
  { map∂ = interp∂ A
  ; mapb = interpb A
  ; unit∂ = refl
  ; unitb = refl
  ; ten∂  = λ _ _ → refl
  ; tenb  = λ _ _ → refl
  ; ext-comm = λ _ → refl
  ; bnd-comm = λ _ → refl
  }

-- (Optional) enriched uniqueness up to preorder can be added per‑model.

-- Initial object interface for ConAlg (up to preorder enrichment)

record InitialConAlg {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
  field
    Free     : ConAlg {ℓ}
    fold     : ∀ (A : ConAlg {ℓ}) → ConAlgHom≡ Free A
    unique   : ∀ (A : ConAlg {ℓ}) (h : ConAlgHom≡ Free A) →
               (∀ x → ConAlgHom≡.map∂ (fold A) x ≡ ConAlgHom≡.map∂ h x) ×
               (∀ d → ConAlgHom≡.mapb (fold A) d ≡ ConAlgHom≡.mapb h d)

initialConAlg : ∀ {ℓ} → InitialConAlg {ℓ}
-- Helper for the uniqueness proof (moved out to support a where mutual block)
uniqueProof : ∀ {ℓ} (A : ConAlg {ℓ}) (h : ConAlgHom≡ FreeConAlg A) →
              (∀ x → ConAlgHom≡.map∂ (fold≡ A) x ≡ ConAlgHom≡.map∂ h x) ×
              (∀ d → ConAlgHom≡.mapb (fold≡ A) d ≡ ConAlgHom≡.mapb h d)
uniqueProof A h = (λ x → uniq∂ x) , (λ d → uniqb d)
  where
    open ConAlgHom≡ h using (map∂; mapb; unit∂; unitb; ten∂; tenb; ext-comm; bnd-comm)
    open ConAlg A
    mutual
      uniq∂ : (x : Con∂) → interp∂ A x ≡ map∂ x
      uniq∂ I∂ = sym unit∂
      uniq∂ (x ⊗∂ y) =
        Eq.trans (cong₂ (ConAlg._⊗∂_ A) (uniq∂ x) (uniq∂ y)) (sym (ten∂ x y))
      uniq∂ (bnd d) =
        Eq.trans (cong (LaxMonoidalAdjunction.bnd (ConAlg.Holo A)) (uniqb d)) (sym (bnd-comm d))
      uniq∂ (C.atom∂ ())

      uniqb : (d : Conb) → interpb A d ≡ mapb d
      uniqb Ib = sym unitb
      uniqb (x ⊗b y) =
        Eq.trans (cong₂ (ConAlg._⊗b_ A) (uniqb x) (uniqb y)) (sym (tenb x y))
      uniqb (ext c) =
        Eq.trans (cong (LaxMonoidalAdjunction.ext (ConAlg.Holo A)) (uniq∂ c)) (sym (ext-comm c))

initialConAlg = record
  { Free  = FreeConAlg
  ; fold  = fold≡
  ; unique = uniqueProof
  }
