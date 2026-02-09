{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Assumptions.Core where

open import LogOS.Prelude
open import LogOS.Prelude using (Σ; _×_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel hiding (Box; decode-Box; box-mono)
open import LogOS.Minimal.Con

-- Assumption packs for conditional meta theorems (non-diagonal).
--
-- Structural packs (DecodeExtensional, provability scaffolding, etc.) live in
-- `LogOS.Theorems.Meta.ConditionalPacks`. The purpose of this file is to keep
-- *actual* axiomatic principles (even if non-diagonal) quarantined under the
-- `Assumptions.*` namespace so stable surfaces cannot reach them transitively.

record BoundaryFix {ℓ}
                   {Sig : LogOSSignature ℓ}
                   {Q : QAdapter ℓ}
                   (K : Kernel Sig Q)
                   : Set (lsuc ℓ) where
  open Kernel K
  private
    CP   = BulkBoundary.bnd BB
    Con∂ = ConPreorder.Con CP
    _⊑_  = ConPreorder._⊑_ CP

  -- Textbook side-condition for fixed-point theorems (Knaster–Tarski / Scott).
  Mono : (Con∂ → Con∂) → Set ℓ
  Mono f = MonoOn CP f

  -- A boundary fixed-point principle (up to the preorder): every monotone endomap
  -- has a fixed point, witnessed as mutual refinement.
  field
    fixH : (f : Con∂ → Con∂) → Mono f → Σ Con∂ (λ c → (c ⊑ f c) × (f c ⊑ c))
