{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.CategoryTheory.Kernel2Cat where

-- A lightweight refinement-2-category interface for kernels (laws not bundled):
-- - 1-cells: kernel morphisms equipped with boundary monotonicity
-- - 2-cells: pointwise refinement on decoded code maps
--
-- See `LogOS.Kernel.Hom2Cat` for the underlying operations.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
import LogOS.Kernel.Hom2Cat as KH₂
open import LogOS.Theorems.CategoryTheory.WrapperCore public
  renaming (Ref2Cat to Kernel2Cat)

Kernel2Cat-instance
  : ∀ {ℓ} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ)
  → Kernel2Cat Sig Q
Kernel2Cat-instance Sig Q =
  RelThin2Cat→Ref2CatCore (KH₂.KernelRelThin2Cat {Sig = Sig} {Q = Q})
