{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.Continuity where

-- Scott continuity and approximant characterization wrappers, lifted from
-- FiniteFirst and OmegaCPO structures provided by a Kernel. These are proven
-- once those structures are supplied.

open import LogOS.Prelude
open import LogOS.Prelude using (_×_; _,_)
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Theorems.Boundary.ContinuityCore as Core

-- Scott continuity wrapper: lifts cont-ω from FiniteFirst in a Kernel.

Flow-continuity-K
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO) (BulkBoundary.bnd (Kernel.BB K)))
    (FF   : (let module GT = Truth.GuardedTruth Sig Q in GT.FiniteFirst) (BulkBoundary.bnd (Kernel.BB K)) (GTruth K) ωCPO)
    (f    : ℕ → ConPreorder.Con (BulkBoundary.bnd (Kernel.BB K)))
  → (mono-chain : ∀ n → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (f n) (f (suc n)))
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
                 (Truth.GuardedCore.GuardedClosure.Flow (GTruth K)
                   (Truth.GuardedCore.OmegaCPO.supω ωCPO f))
                 (Truth.GuardedCore.OmegaCPO.supω ωCPO
                   (λ n → Truth.GuardedCore.GuardedClosure.Flow (GTruth K) (f n)))
Flow-continuity-K Sig Q K ωCPO FF f mono =
  let module C = Core.For (BulkBoundary.bnd (Kernel.BB K)) (GTruth K)
  in C.Flow-continuity ωCPO FF f mono

-- Textbook aliases.

scott-continuity-K = Flow-continuity-K
ω-continuity-K = Flow-continuity-K

-- Approximant characterization of Th* in a Kernel.

Th*-as-sup-K
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO) (BulkBoundary.bnd (Kernel.BB K)))
    (FF   : (let module GT = Truth.GuardedTruth Sig Q in GT.FiniteFirst) (BulkBoundary.bnd (Kernel.BB K)) (GTruth K) ωCPO)
  → (ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
        (Truth.GuardedCore.GuardedClosure.Th* (GTruth K))
        (Truth.GuardedCore.OmegaCPO.supω ωCPO (Truth.GuardedCore.FiniteFirst.approxS FF)))
    ×
    (ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
        (Truth.GuardedCore.OmegaCPO.supω ωCPO (Truth.GuardedCore.FiniteFirst.approxS FF))
        (Truth.GuardedCore.GuardedClosure.Th* (GTruth K)))
Th*-as-sup-K Sig Q K ωCPO FF =
  let module C = Core.For (BulkBoundary.bnd (Kernel.BB K)) (GTruth K)
  in C.Th*-as-sup ωCPO FF

-- Textbook aliases (Kleene approximation theorem).
-- Interprets Th⋆ as the ω-supremum of its finite approximants, up to the preorder.

kleene-approximation-K = Th*-as-sup-K
kleene-fixedpoint-K = Th*-as-sup-K

-- Kleene μ characterisation of Th* in a Kernel (up to the preorder).
--
-- Under `FiniteFirst`, the chosen approximants satisfy the same defining
-- equations as the Kleene iterates, hence `Th* ≈ μ Flow`.

Th*-as-μFlow-K
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO) (BulkBoundary.bnd (Kernel.BB K)))
    (FF   : (let module GT = Truth.GuardedTruth Sig Q in GT.FiniteFirst) (BulkBoundary.bnd (Kernel.BB K)) (GTruth K) ωCPO)
  → (ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
        (Truth.GuardedCore.GuardedClosure.Th* (GTruth K))
        (Truth.GuardedCore.Kleene.μ ωCPO (Truth.GuardedCore.GuardedClosure.Flow (GTruth K))))
    ×
    (ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
        (Truth.GuardedCore.Kleene.μ ωCPO (Truth.GuardedCore.GuardedClosure.Flow (GTruth K)))
        (Truth.GuardedCore.GuardedClosure.Th* (GTruth K)))
Th*-as-μFlow-K Sig Q K ωCPO FF =
  let module C = Core.For (BulkBoundary.bnd (Kernel.BB K)) (GTruth K)
  in C.Th*-as-μFlow ωCPO FF

kleene-μ-K = Th*-as-μFlow-K

-- Convenience projections / notation.

Th*≈μFlow-K = Th*-as-μFlow-K

Th*≤μFlow-K
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO) (BulkBoundary.bnd (Kernel.BB K)))
    (FF   : (let module GT = Truth.GuardedTruth Sig Q in GT.FiniteFirst) (BulkBoundary.bnd (Kernel.BB K)) (GTruth K) ωCPO)
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Truth.GuardedCore.GuardedClosure.Th* (GTruth K))
      (Truth.GuardedCore.Kleene.μ ωCPO (Truth.GuardedCore.GuardedClosure.Flow (GTruth K)))
Th*≤μFlow-K Sig Q K ωCPO FF = fst (Th*-as-μFlow-K Sig Q K ωCPO FF)

μFlow≤Th*-K
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO) (BulkBoundary.bnd (Kernel.BB K)))
    (FF   : (let module GT = Truth.GuardedTruth Sig Q in GT.FiniteFirst) (BulkBoundary.bnd (Kernel.BB K)) (GTruth K) ωCPO)
  → ConPreorder._⊑_ (BulkBoundary.bnd (Kernel.BB K))
      (Truth.GuardedCore.Kleene.μ ωCPO (Truth.GuardedCore.GuardedClosure.Flow (GTruth K)))
      (Truth.GuardedCore.GuardedClosure.Th* (GTruth K))
μFlow≤Th*-K Sig Q K ωCPO FF = snd (Th*-as-μFlow-K Sig Q K ωCPO FF)
