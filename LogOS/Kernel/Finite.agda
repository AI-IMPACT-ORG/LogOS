{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Finite where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel

-- Naming clarity: the existing `Kernel` record is the “finite/minimal kernel”
-- (it does not require ω-chain completeness / dcpo structure on the boundary).

FiniteKernel : ∀ {ℓ} → (Sig : LogOSSignature ℓ) → (Q : QAdapter ℓ) → Set (lsuc (lsuc ℓ))
FiniteKernel Sig Q = Kernel Sig Q
