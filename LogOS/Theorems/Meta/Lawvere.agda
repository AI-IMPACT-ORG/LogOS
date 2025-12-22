{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Lawvere where

open import LogOS.Prelude
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; fst; snd)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con using (ConPoset; BulkBoundary)
open import LogOS.Kernel

open import LogOS.Theorems.Meta.Assumptions.Core using
  ( Provability
  ; ProvabilityOps
  )

open import LogOS.Theorems.Meta.Assumptions.Diagonal using
  ( QuoteSubst⊑
  ; DecodeImp⊑
  ; Diagonalization
  )

-- Lawvere fixed point, specialized to the LogOS “code-as-internal-hom witness”.
--
-- Intuition:
--   - `QuoteSubst⊑ K` is a syntactic, internal-hom-style representation:
--       * `Code₁` are “single-hole templates”
--       * `inst u γ` is application / plugging `γ` into template `u`
--       * `representable` says every endomap is represented by some template
--       * `self` gives a “self-application” code for any template
--   - From this, fixed points (and hence diagonalization) are theorems, not axioms.
--
-- NOTE: `representable` ranges over Agda-level endomaps `Code → Code`. This is
-- intentionally an explicit, model-local assumption.
--
-- NOTE: We never assume antisymmetry of the underlying constraint preorder.

InternalHomWitness
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
  → Set (lsuc ℓ)
InternalHomWitness = QuoteSubst⊑

-- Core Lawvere fixed-point: produce a self-referential code whose boundary meaning
-- is a fixed point of any represented endomap (up to mutual refinement in the preorder).

lawvereFix
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → InternalHomWitness K
  → (f : Kernel.Code K → Kernel.Code K)
  → Σ (Kernel.Code K) (λ s →
      ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
        (Kernel.decode K s) (Kernel.decode K (f s))
      ×
      ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
        (Kernel.decode K (f s)) (Kernel.decode K s))
lawvereFix {K = K} QS f =
  let
    open Kernel K
    open QuoteSubst⊑ QS

    rep  = representable f
    u    = proj₁ rep
    repr = proj₂ rep
    se   = self u
    s    = proj₁ se

    selfL = fst (proj₂ se)
    selfR = snd (proj₂ se)
    reprL = fst (repr s)
    reprR = snd (repr s)
    left  = ConPoset.trans (BulkBoundary.bnd BB) selfL reprL
    right = ConPoset.trans (BulkBoundary.bnd BB) reprR selfR
  in
  s , (left , right)

-- A convenient “diag” presentation used by demos: a canonical fixed point chooser.

diag : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
       {K : Kernel Sig Q}
     → InternalHomWitness K
     → (Kernel.Code K → Kernel.Code K)
     → Kernel.Code K
diag QS f = proj₁ (lawvereFix QS f)

diag-⊑
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → (QS : InternalHomWitness K)
  → (f  : Kernel.Code K → Kernel.Code K)
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Kernel.decode K (diag QS f))
      (Kernel.decode K (f (diag QS f)))
diag-⊑ QS f = fst (proj₂ (lawvereFix QS f))

⊑-diag
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    {K : Kernel Sig Q}
  → (QS : InternalHomWitness K)
  → (f  : Kernel.Code K → Kernel.Code K)
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Kernel.decode K (f (diag QS f)))
      (Kernel.decode K (diag QS f))
⊑-diag QS f = snd (proj₂ (lawvereFix QS f))

-- Provability-level diagonalization as a theorem:
-- internal hom witness + local decode→imp bridge ⇒ the classical diagonal schema.

Diagonalization-from-InternalHom
  : ∀ {ℓ} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K  : Kernel Sig Q)
    (Pr : Provability K)
    (Op : ProvabilityOps K)
    (IH : InternalHomWitness K)
    (DI : DecodeImp⊑ K Pr Op)
  → Diagonalization K Pr Op
Diagonalization-from-InternalHom K Pr Op IH DI = record
  { diag  = λ f → diag IH f
  ; diag→ = λ f → DecodeImp⊑.from-decode⊑→imp DI (diag-⊑ IH f)
  ; →diag = λ f → DecodeImp⊑.from-decode⊑→imp DI (⊑-diag IH f)
  }
