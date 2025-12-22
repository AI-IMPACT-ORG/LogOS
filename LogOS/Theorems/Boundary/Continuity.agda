{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.Continuity where

-- Scott continuity and approximant characterization wrappers, lifted from
-- FiniteFirst and OmegaCPO structures provided by a Kernel. These are proven
-- once those structures are supplied.

open import LogOS.Prelude
open import Data.Product using (_×_; _,_)
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Truth as Truth
open import LogOS.Minimal.Con
open import LogOS.Kernel
open import LogOS.Kernel.Endo

-- Scott continuity wrapper: lifts cont-ω from FiniteFirst in a Kernel.

Flow-continuity-K
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO) (BulkBoundary.bnd (Kernel.BB K)))
    (FF   : (let module GT = Truth.GuardedTruth Sig Q in GT.FiniteFirst) (BulkBoundary.bnd (Kernel.BB K)) (Kernel.GTruth K) ωCPO)
    (f    : ℕ → ConPoset.Con (BulkBoundary.bnd (Kernel.BB K)))
  → (mono-chain : ∀ n → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K)) (f n) (f (suc n)))
  → ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
                 (Endo.fn (Flow-Endo K)
                   (Truth.GuardedCore.OmegaCPO.supω ωCPO f))
                 (Truth.GuardedCore.OmegaCPO.supω ωCPO (λ n → Endo.fn (Flow-Endo K) (f n)))
Flow-continuity-K Sig Q K ωCPO FF f mono =
  Truth.GuardedCore.FiniteFirst.cont-ω FF f mono

-- Textbook aliases.

scott-continuity-K = Flow-continuity-K
ω-continuity-K = Flow-continuity-K

-- Approximant characterization of Th* in a Kernel.

Th*-as-sup-K
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
    (K : Kernel Sig Q)
    (ωCPO : (let module GT = Truth.GuardedTruth Sig Q in GT.OmegaCPO) (BulkBoundary.bnd (Kernel.BB K)))
    (FF   : (let module GT = Truth.GuardedTruth Sig Q in GT.FiniteFirst) (BulkBoundary.bnd (Kernel.BB K)) (Kernel.GTruth K) ωCPO)
  → (ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
        (Th⋆K K)
        (Truth.GuardedCore.OmegaCPO.supω ωCPO (Truth.GuardedCore.FiniteFirst.approxS FF)))
    ×
    (ConPoset._⊑_ (BulkBoundary.bnd (Kernel.BB K))
        (Truth.GuardedCore.OmegaCPO.supω ωCPO (Truth.GuardedCore.FiniteFirst.approxS FF))
        (Th⋆K K))
Th*-as-sup-K Sig Q K ωCPO FF = Truth.GuardedCore.FiniteFirst.Th⋆-as-sup FF

-- Textbook aliases (Kleene approximation theorem).
-- Interprets Th⋆ as the ω-supremum of its finite approximants, up to the preorder.

kleene-approximation-K = Th*-as-sup-K
kleene-fixedpoint-K = Th*-as-sup-K
