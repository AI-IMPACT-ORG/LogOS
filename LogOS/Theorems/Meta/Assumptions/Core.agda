{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Assumptions.Core where

open import LogOS.Prelude
open import Data.Product using (Σ)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel
open import LogOS.Minimal.Con
open import LogOS.Theorems.Meta.Base using (NonTrivialC)

-- Shared assumption packs for conditional meta theorems.
--
-- This module is intentionally “structural”: it contains only the minimal packs
-- that do not themselves introduce diagonalisation/self-reference principles.

DecodeExtensional
  : ∀ {ℓ ℓP} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
    (K : Kernel Sig Q)
    (P : Kernel.Code K → Set ℓP)
  → Set (ℓ ⊔ ℓP)
DecodeExtensional K P =
  ∀ γ₁ γ₂ → Kernel.decode K γ₁ ≡ Kernel.decode K γ₂ → P γ₁ → P γ₂

record BoundaryFix {ℓ}
                   {Sig : LogOSSignature ℓ}
                   {Q : QAdapter ℓ}
                   (K : Kernel Sig Q)
                   : Set (lsuc ℓ) where
  open Kernel K
  private
    CP   = BulkBoundary.bnd BB
    Con∂ = ConPoset.Con CP
    _⊑_  = ConPoset._⊑_ CP

  -- Textbook side-condition for fixed-point theorems (Knaster–Tarski / Scott).
  Mono : (Con∂ → Con∂) → Set ℓ
  Mono f = MonoOn CP f

  -- A boundary fixed-point principle (up to the preorder): every monotone endomap
  -- has a fixed point, witnessed as mutual refinement.
  field
    fixH : (f : Con∂ → Con∂) → Mono f → Σ Con∂ (λ c → (c ⊑ f c) × (f c ⊑ c))

record Provability {ℓ}
                   {Sig : LogOSSignature ℓ}
                   {Q : QAdapter ℓ}
                   (K : Kernel Sig Q)
                   : Set (lsuc ℓ) where
  field
    Prov    : Kernel.Code K → Set ℓ
    ext     : DecodeExtensional K Prov
    nontriv : NonTrivialC {K = K} Prov

record ProvabilityOps {ℓ}
                      {Sig : LogOSSignature ℓ}
                      {Q : QAdapter ℓ}
                      (K : Kernel Sig Q)
                      : Set (lsuc ℓ) where
  open Kernel K
  field
    Imp : Code → Code → Code
    Box : Code → Code

-- HBL (classic):
-- 1) Necessitation: if ⊢ φ then ⊢ Box φ
-- 2) Distribution (K): ⊢ Box(φ → ψ) → (Box φ → Box ψ)
-- 3) 4-axiom: ⊢ Box φ → Box Box φ

record HBLClassic {ℓ}
                  {Sig : LogOSSignature ℓ}
                  {Q   : QAdapter ℓ}
                  (K  : Kernel Sig Q)
                  (Pr : Provability K)
                  (Op : ProvabilityOps K)
                  : Set (lsuc ℓ) where
  open Provability Pr renaming (Prov to ⊢)
  open ProvabilityOps Op
  field
    Necessitation : ∀ φ → ⊢ φ → ⊢ (Box φ)
    Kdist         : ∀ φ ψ → ⊢ (Imp φ ψ) → (⊢ (Box φ) → ⊢ (Box ψ))
    Four          : ∀ φ → ⊢ (Box φ) → ⊢ (Box (Box φ))
