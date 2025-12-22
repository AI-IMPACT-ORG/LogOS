{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.Graded.Mu where

-- Guarded μ-unfold and μ-induction wrappers instantiated at a graded kernel.
-- All proofs are inherited directly from `LogOS.Minimal.Truth` once a graded
-- kernel supplies the required GradedClosure/OmegaCPO/FiniteFirst records.

open import LogOS.Prelude
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import Data.Product using (_×_; _,_; fst; snd)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.Con
open import LogOS.Kernel.Graded

-- Lax μ-induction rule instantiated at a graded kernel with OmegaCPO + FiniteFirst.
--
-- Textbook correspondence (at saturation grade):
-- - Park induction / least prefixed point principle:
--     if Flow sat c ⊑ c then Th⋆ ⊑ c.

μ-induction-K
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : GradedKernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO) (BulkBoundary.bnd (GradedKernel.BB K)))
    (FF   : (let module GT = Truth.GuardedCore in GT.FiniteFirst)
             (BulkBoundary.bnd (GradedKernel.BB K))
             (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K)) ωCPO)
    (c    : ConPoset.Con (BulkBoundary.bnd (GradedKernel.BB K)))
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
                 (GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K)) c)
                 c
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
                 (GradedClosure.Th* (GradedKernel.GTruth K))
                 c
μ-induction-K Sig Q K ωCPO FF c pre =
  let module GT = Truth.GuardedCore
      GC = GT.forgetGradedClosure (GradedKernel.GTruth K)
  in GT.μ-induction {CP = BulkBoundary.bnd (GradedKernel.BB K)} GC ωCPO FF c pre

-- Classic aliases (textbook names).

park-induction-K
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : GradedKernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO) (BulkBoundary.bnd (GradedKernel.BB K)))
    (FF   : (let module GT = Truth.GuardedCore in GT.FiniteFirst)
             (BulkBoundary.bnd (GradedKernel.BB K))
             (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K)) ωCPO)
    (c    : ConPoset.Con (BulkBoundary.bnd (GradedKernel.BB K)))
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
                 (GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K)) c)
                 c
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
                 (GradedClosure.Th* (GradedKernel.GTruth K))
                 c
park-induction-K = μ-induction-K

least-prefixed-point-K = park-induction-K

-- Unfolding laws for Th* in any graded kernel (re-exported as theorems).

μ-unfold-left
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : GradedKernel Sig Q)
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
                 (GradedClosure.Th* (GradedKernel.GTruth K))
                 (GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K))
                   (GradedClosure.Th* (GradedKernel.GTruth K)))
μ-unfold-left Sig Q K = fst (GradedClosure.Th*-fixed (GradedKernel.GTruth K))

μ-unfold-right
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : GradedKernel Sig Q)
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
                 (GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K))
                   (GradedClosure.Th* (GradedKernel.GTruth K)))
                 (GradedClosure.Th* (GradedKernel.GTruth K))
μ-unfold-right Sig Q K = snd (GradedClosure.Th*-fixed (GradedKernel.GTruth K))
