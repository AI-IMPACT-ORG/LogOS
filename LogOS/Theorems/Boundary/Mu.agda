{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.Mu where

-- Guarded μ-unfold and μ-induction wrappers instantiated at a Kernel.
-- All proofs are inherited directly from `LogOS.Minimal.Truth` once a Kernel
-- supplies the required GuardedClosure/OmegaCPO/FiniteFirst records.

open import LogOS.Prelude
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import Data.Product using (_×_; _,_; fst; snd)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Kernel.Endo

-- Lax μ-induction rule instantiated at a Kernel with OmegaCPO + FiniteFirst.
--
-- Textbook correspondence:
-- - Park induction / least prefixed point principle:
--     if Flow c ⊑ c then Th⋆ ⊑ c.

μ-induction-K
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO) (BulkBoundary.bnd (Kernel.BB K)))
    (FF   : (let module GT = Truth.GuardedTruth Sig Q in GT.FiniteFirst) (BulkBoundary.bnd (Kernel.BB K)) (Kernel.GTruth K) ωCPO)
    (c    : ConPoset.Con (BulkBoundary.bnd (Kernel.BB K)))
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
                 (Endo.fn (Flow-Endo K) c)
                 c
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
                 (Th⋆K K)
                 c
μ-induction-K Sig Q K ωCPO FF c pre =
  let module GT = Truth.GuardedTruth Sig Q in
  GT.μ-induction {CP = BulkBoundary.bnd (Kernel.BB K)} (Kernel.GTruth K) ωCPO FF c pre

-- Classic aliases (textbook names).

park-induction-K
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO) (BulkBoundary.bnd (Kernel.BB K)))
    (FF   : (let module GT = Truth.GuardedTruth Sig Q in GT.FiniteFirst) (BulkBoundary.bnd (Kernel.BB K)) (Kernel.GTruth K) ωCPO)
    (c    : ConPoset.Con (BulkBoundary.bnd (Kernel.BB K)))
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
                 (Endo.fn (Flow-Endo K) c)
                 c
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
                 (Th⋆K K)
                 c
park-induction-K = μ-induction-K

least-prefixed-point-K = park-induction-K

-- Unfolding laws for Th* in any Kernel (re-exported as theorems)

μ-unfold-left
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (Th⋆K K) (FlowTh⋆K K)
μ-unfold-left Sig Q K = Th⋆≤FlowTh⋆ K

μ-unfold-right
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (FlowTh⋆K K) (Th⋆K K)
μ-unfold-right Sig Q K = FlowTh⋆≤Th⋆ K
