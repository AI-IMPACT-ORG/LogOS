{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.Graded.Continuity where

-- Scott continuity and approximant characterization wrappers, lifted from
-- FiniteFirst and OmegaCPO structures provided by a graded kernel (via
-- saturation-grade forgetting).

open import LogOS.Prelude
open import Data.Product using (_×_; _,_)
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.Con
open import LogOS.Kernel.Graded

-- Scott continuity wrapper: lifts cont-ω from FiniteFirst in a graded kernel.

Flow-continuity-K
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : GradedKernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO) (BulkBoundary.bnd (GradedKernel.BB K)))
    (FF   : (let module GT = Truth.GuardedCore in GT.FiniteFirst)
             (BulkBoundary.bnd (GradedKernel.BB K))
             (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K)) ωCPO)
    (f    : ℕ → ConPoset.Con (BulkBoundary.bnd (GradedKernel.BB K)))
  → (mono-chain : ∀ n → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K)) (f n) (f (suc n)))
  → ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
                 (GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K))
                   (Truth.GuardedCore.OmegaCPO.supω ωCPO f))
                 (Truth.GuardedCore.OmegaCPO.supω ωCPO
                   (λ n → GradedClosure.Flow (GradedKernel.GTruth K) (GradedClosure.sat (GradedKernel.GTruth K)) (f n)))
Flow-continuity-K Sig Q K ωCPO FF f mono =
  Truth.GuardedCore.FiniteFirst.cont-ω FF f mono

-- Textbook aliases.

scott-continuity-K = Flow-continuity-K
ω-continuity-K = Flow-continuity-K

-- Approximant characterization of Th* in a graded kernel.

Th*-as-sup-K
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : GradedKernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO) (BulkBoundary.bnd (GradedKernel.BB K)))
    (FF   : (let module GT = Truth.GuardedCore in GT.FiniteFirst)
             (BulkBoundary.bnd (GradedKernel.BB K))
             (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K)) ωCPO)
  → (ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
        (GradedClosure.Th* (GradedKernel.GTruth K))
        (Truth.GuardedCore.OmegaCPO.supω ωCPO (Truth.GuardedCore.FiniteFirst.approxS FF)))
    ×
    (ConPoset._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
        (Truth.GuardedCore.OmegaCPO.supω ωCPO (Truth.GuardedCore.FiniteFirst.approxS FF))
        (GradedClosure.Th* (GradedKernel.GTruth K)))
Th*-as-sup-K Sig Q K ωCPO FF = Truth.GuardedCore.FiniteFirst.Th⋆-as-sup FF

-- Textbook aliases (Kleene approximation theorem).

kleene-approximation-K = Th*-as-sup-K
kleene-fixedpoint-K = Th*-as-sup-K
