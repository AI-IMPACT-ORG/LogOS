{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.Graded.Continuity where

-- Scott continuity and approximant characterization wrappers, lifted from
-- FiniteFirst and OmegaCPO structures provided by a graded kernel (via
-- saturation-grade forgetting).

open import LogOS.Prelude
open import LogOS.Prelude.Product using (_×_; _,_)
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.Con
open import LogOS.Kernel.Graded
open import LogOS.Theorems.Boundary.ContinuityCore as Core

-- Scott continuity wrapper: lifts cont-ω from FiniteFirst in a graded kernel.

Flow-continuity-K
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : GradedKernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO) (BulkBoundary.bnd (GradedKernel.BB K)))
    (FF   : (let module GT = Truth.GuardedCore in GT.FiniteFirst)
             (BulkBoundary.bnd (GradedKernel.BB K))
             (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K)) ωCPO)
    (f    : ℕ → ConPreorder.Con (BulkBoundary.bnd (GradedKernel.BB K)))
  → (mono-chain : ∀ n → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K)) (f n) (f (suc n)))
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
                 (Truth.GuardedCore.GuardedClosure.Flow
                   (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K))
                   (Truth.GuardedCore.OmegaCPO.supω ωCPO f))
                 (Truth.GuardedCore.OmegaCPO.supω ωCPO
                   (λ n →
                     Truth.GuardedCore.GuardedClosure.Flow
                       (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K)) (f n)))
Flow-continuity-K Sig Q K ωCPO FF f mono =
  let module C =
        Core.For (BulkBoundary.bnd (GradedKernel.BB K))
                 (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K))
  in C.Flow-continuity ωCPO FF f mono

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
  → (ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
        (Truth.GuardedCore.GuardedClosure.Th*
          (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K)))
        (Truth.GuardedCore.OmegaCPO.supω ωCPO (Truth.GuardedCore.FiniteFirst.approxS FF)))
    ×
    (ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
        (Truth.GuardedCore.OmegaCPO.supω ωCPO (Truth.GuardedCore.FiniteFirst.approxS FF))
        (Truth.GuardedCore.GuardedClosure.Th*
          (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K))))
Th*-as-sup-K Sig Q K ωCPO FF =
  let module C =
        Core.For (BulkBoundary.bnd (GradedKernel.BB K))
                 (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K))
  in C.Th*-as-sup ωCPO FF

-- Textbook aliases (Kleene approximation theorem).

kleene-approximation-K = Th*-as-sup-K
kleene-fixedpoint-K = Th*-as-sup-K

-- Kleene μ characterisation of Th* in a graded kernel (at saturation grade,
-- up to the preorder), via the `forgetGradedClosure` view.

Th*-as-μFlow-K
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : GradedKernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO) (BulkBoundary.bnd (GradedKernel.BB K)))
    (FF   : (let module GT = Truth.GuardedCore in GT.FiniteFirst)
             (BulkBoundary.bnd (GradedKernel.BB K))
             (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K)) ωCPO)
  → (ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
        (Truth.GuardedCore.GuardedClosure.Th*
          (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K)))
        (Truth.GuardedCore.Kleene.μ ωCPO
          (Truth.GuardedCore.GuardedClosure.Flow
            (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K)))))
    ×
    (ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
        (Truth.GuardedCore.Kleene.μ ωCPO
          (Truth.GuardedCore.GuardedClosure.Flow
            (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K))))
        (Truth.GuardedCore.GuardedClosure.Th*
          (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K))))
Th*-as-μFlow-K Sig Q K ωCPO FF =
  let module C =
        Core.For (BulkBoundary.bnd (GradedKernel.BB K))
                 (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K))
  in C.Th*-as-μFlow ωCPO FF

kleene-μ-K = Th*-as-μFlow-K

-- Convenience projections / notation (at saturation grade, via `forgetGradedClosure`).

Th*≈μFlow-K = Th*-as-μFlow-K

Th*≤μFlow-K
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : GradedKernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO) (BulkBoundary.bnd (GradedKernel.BB K)))
    (FF   : (let module GT = Truth.GuardedCore in GT.FiniteFirst)
             (BulkBoundary.bnd (GradedKernel.BB K))
             (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K)) ωCPO)
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (Truth.GuardedCore.GuardedClosure.Th*
        (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K)))
      (Truth.GuardedCore.Kleene.μ ωCPO
        (Truth.GuardedCore.GuardedClosure.Flow
          (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K))))
Th*≤μFlow-K Sig Q K ωCPO FF = fst (Th*-as-μFlow-K Sig Q K ωCPO FF)

μFlow≤Th*-K
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : GradedKernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO) (BulkBoundary.bnd (GradedKernel.BB K)))
    (FF   : (let module GT = Truth.GuardedCore in GT.FiniteFirst)
             (BulkBoundary.bnd (GradedKernel.BB K))
             (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K)) ωCPO)
  → ConPreorder._⊑_ (BulkBoundary.bnd (GradedKernel.BB K))
      (Truth.GuardedCore.Kleene.μ ωCPO
        (Truth.GuardedCore.GuardedClosure.Flow
          (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K))))
      (Truth.GuardedCore.GuardedClosure.Th*
        (Truth.GuardedCore.forgetGradedClosure (GradedKernel.GTruth K)))
μFlow≤Th*-K Sig Q K ωCPO FF = snd (Th*-as-μFlow-K Sig Q K ωCPO FF)
