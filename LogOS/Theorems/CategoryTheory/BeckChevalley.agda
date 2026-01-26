{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.CategoryTheory.BeckChevalley where

-- “Hyperdoctrine-shaped” coherence, without importing full Lawvere semantics.
--
-- We model the Beck–Chevalley principle in a conservative, preorder-enriched way:
-- a pair of maps (boundary/bulk) commutes with the (lax) adjunction operations
-- `ext ⊣ bnd` up to refinement, and therefore preserves the derived closure
-- operator `T = bnd ∘ ext` and the derived interior `S = ext ∘ bnd` up to
-- refinement, once the *target* `bnd`/`ext` maps are assumed monotone.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (ConPreorder; BulkBoundary; MonoMap)
open import LogOS.Minimal.Adjunction using (LaxAdjunction; LaxMonoidalAdjunction)
open import LogOS.Algebra.ConAlg using (ConAlgHom≡)
open import LogOS.Kernel using (Kernel)
open import LogOS.Kernel.Hom using (KernelHom)

module For
  {ℓ : Level}
  {BB₁ BB₂ : BulkBoundary ℓ}
  (A : LaxAdjunction BB₁)
  (B : LaxAdjunction BB₂)
  where

  open BulkBoundary BB₁ renaming (Con_bnd to Con∂₁; Con_bulk to Conb₁; _⊑bnd_ to _≤∂₁_; _⊑bulk_ to _≤b₁_)
  open BulkBoundary BB₂ renaming (Con_bnd to Con∂₂; Con_bulk to Conb₂; _⊑bnd_ to _≤∂₂_; _⊑bulk_ to _≤b₂_)

  open LaxAdjunction A renaming (ext to ext₁; bnd to bnd₁)
  open LaxAdjunction B renaming (ext to ext₂; bnd to bnd₂)

  -- Lax Beck–Chevalley data: commutation squares for `ext` and `bnd` up to ≤.
  --
  -- This is intentionally one-way (lax) to avoid collapsing irreversible
  -- structure. If you have both directions, you can upgrade to an `≈`-level
  -- statement (mutual refinement) separately.

  record BeckChevalleySquaresLax : Set (lsuc ℓ) where
    field
      map∂ : Con∂₁ → Con∂₂
      mapb : Conb₁ → Conb₂

      ext-lax : ∀ c → _≤b₂_ (mapb (ext₁ c)) (ext₂ (map∂ c))
      bnd-lax : ∀ d → _≤∂₂_ (map∂ (bnd₁ d)) (bnd₂ (mapb d))

  -- Optional strengthening: monotonicity of the boundary/bulk maps.
  --
  -- The closure/interior preservation lemmas below only need the commutation
  -- squares; monotonicity is threaded separately so that strict maps (equality
  -- preservation) can be used as Beck–Chevalley squares without additionally
  -- proving preorder monotonicity.

  record BeckChevalleyLax : Set (lsuc ℓ) where
    field
      squares : BeckChevalleySquaresLax
      mono∂ : MonoMap (BulkBoundary.bnd BB₁) (BulkBoundary.bnd BB₂) (BeckChevalleySquaresLax.map∂ squares)
      monob : MonoMap (BulkBoundary.bulk BB₁) (BulkBoundary.bulk BB₂) (BeckChevalleySquaresLax.mapb squares)

    open BeckChevalleySquaresLax squares public

  open BeckChevalleySquaresLax public

  -- Textbook abbreviations (to make statements read more like “BC/Frob” lore).

  BCSquaresLax : Set (lsuc ℓ)
  BCSquaresLax = BeckChevalleySquaresLax

  BCLax : Set (lsuc ℓ)
  BCLax = BeckChevalleyLax

  -- Derived closure/interior operators (quantifier-like).

  T₁ : Con∂₁ → Con∂₁
  T₁ c = bnd₁ (ext₁ c)

  T₂ : Con∂₂ → Con∂₂
  T₂ c = bnd₂ (ext₂ c)

  S₁ : Conb₁ → Conb₁
  S₁ d = ext₁ (bnd₁ d)

  S₂ : Conb₂ → Conb₂
  S₂ d = ext₂ (bnd₂ d)

  -- Beck–Chevalley consequence: `map∂` preserves the boundary closure `T` up to ≤.

  map∂-T-lax
    : (bnd₂-mono : MonoMap (BulkBoundary.bulk BB₂) (BulkBoundary.bnd BB₂) bnd₂)
    → (BC : BeckChevalleySquaresLax)
    → ∀ c → _≤∂₂_ (map∂ BC (T₁ c)) (T₂ (map∂ BC c))
  map∂-T-lax bnd₂-mono BC c =
    ConPreorder.trans (BulkBoundary.bnd BB₂)
      (bnd-lax BC (ext₁ c))
      (bnd₂-mono (ext-lax BC c))

  -- Beck–Chevalley consequence: `mapb` preserves the bulk interior `S` up to ≤.

  mapb-S-lax
    : (ext₂-mono : MonoMap (BulkBoundary.bnd BB₂) (BulkBoundary.bulk BB₂) ext₂)
    → (BC : BeckChevalleySquaresLax)
    → ∀ d → _≤b₂_ (mapb BC (S₁ d)) (S₂ (mapb BC d))
  mapb-S-lax ext₂-mono BC d =
    ConPreorder.trans (BulkBoundary.bulk BB₂)
      (ext-lax BC (bnd₁ d))
      (ext₂-mono (bnd-lax BC d))

  -- Convenience wrappers: use a full Beck–Chevalley structure directly.

  map∂-T-lax′
    : (bnd₂-mono : MonoMap (BulkBoundary.bulk BB₂) (BulkBoundary.bnd BB₂) bnd₂)
    → (BC : BeckChevalleyLax)
    → ∀ c → _≤∂₂_ (BeckChevalleyLax.map∂ BC (T₁ c)) (T₂ (BeckChevalleyLax.map∂ BC c))
  map∂-T-lax′ bnd₂-mono BC = map∂-T-lax bnd₂-mono (BeckChevalleyLax.squares BC)

  mapb-S-lax′
    : (ext₂-mono : MonoMap (BulkBoundary.bnd BB₂) (BulkBoundary.bulk BB₂) ext₂)
    → (BC : BeckChevalleyLax)
    → ∀ d → _≤b₂_ (BeckChevalleyLax.mapb BC (S₁ d)) (S₂ (BeckChevalleyLax.mapb BC d))
  mapb-S-lax′ ext₂-mono BC = mapb-S-lax ext₂-mono (BeckChevalleyLax.squares BC)

-- -------------------------------------------------------------------------
-- Kernel bridge: any kernel hom gives Beck–Chevalley squares (lax).
-- -------------------------------------------------------------------------

module FromKernelHom
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  {K₁ K₂ : Kernel Sig Q}
  (h : KernelHom K₁ K₂)
  where

  private
    BB₁ = Kernel.BB K₁
    BB₂ = Kernel.BB K₂

    A : LaxAdjunction BB₁
    A = LaxMonoidalAdjunction.core (Kernel.Holo K₁)

    B : LaxAdjunction BB₂
    B = LaxMonoidalAdjunction.core (Kernel.Holo K₂)

    ≡⇒⊑
      : ∀ {ℓCP}
        {CP : ConPreorder ℓCP}
        {x y : ConPreorder.Con CP}
      → x ≡ y
      → ConPreorder._⊑_ CP x y
    ≡⇒⊑ {CP = CP} refl = ConPreorder.refl CP

  module BC = For A B

  squares : BC.BeckChevalleySquaresLax
  squares =
    record
      { map∂ = ConAlgHom≡.map∂ (KernelHom.con-hom h)
      ; mapb = ConAlgHom≡.mapb (KernelHom.con-hom h)
      ; ext-lax = λ c → ≡⇒⊑ {CP = BulkBoundary.bulk BB₂} (ConAlgHom≡.ext-comm (KernelHom.con-hom h) c)
      ; bnd-lax = λ d → ≡⇒⊑ {CP = BulkBoundary.bnd BB₂} (ConAlgHom≡.bnd-comm (KernelHom.con-hom h) d)
      }

  -- Downstream-ready consequence: kernel homs preserve the target boundary
  -- closure `T = bnd ∘ ext` up to refinement, provided the target `bnd` is
  -- monotone (the only extra assumption required).

  map∂-T-lax
    : (bnd₂-mono : MonoMap
        (BulkBoundary.bulk (Kernel.BB K₂))
        (BulkBoundary.bnd (Kernel.BB K₂))
        (LaxMonoidalAdjunction.bnd (Kernel.Holo K₂)))
    → ∀ c
    → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K₂))
        (ConAlgHom≡.map∂ (KernelHom.con-hom h)
          (LaxMonoidalAdjunction.bnd (Kernel.Holo K₁)
            (LaxMonoidalAdjunction.ext (Kernel.Holo K₁) c)))
        (LaxMonoidalAdjunction.bnd (Kernel.Holo K₂)
          (LaxMonoidalAdjunction.ext (Kernel.Holo K₂)
            (ConAlgHom≡.map∂ (KernelHom.con-hom h) c)))
  map∂-T-lax bnd₂-mono c = BC.map∂-T-lax bnd₂-mono squares c

  -- Dual: kernel homs preserve the target bulk interior `S = ext ∘ bnd` up to
  -- refinement, provided the target `ext` is monotone.
  mapb-S-lax
    : (ext₂-mono : MonoMap
        (BulkBoundary.bnd (Kernel.BB K₂))
        (BulkBoundary.bulk (Kernel.BB K₂))
        (LaxMonoidalAdjunction.ext (Kernel.Holo K₂)))
    → ∀ d
    → ConPreorder._⊑_ (BulkBoundary.bulk (Kernel.BB K₂))
        (ConAlgHom≡.mapb (KernelHom.con-hom h)
          (LaxMonoidalAdjunction.ext (Kernel.Holo K₁)
            (LaxMonoidalAdjunction.bnd (Kernel.Holo K₁) d)))
        (LaxMonoidalAdjunction.ext (Kernel.Holo K₂)
          (LaxMonoidalAdjunction.bnd (Kernel.Holo K₂)
            (ConAlgHom≡.mapb (KernelHom.con-hom h) d)))
  mapb-S-lax ext₂-mono d = BC.mapb-S-lax ext₂-mono squares d
