{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Capstone.Approximation where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Kernel.Endo
open import LogOS.Kernel.UngradedKernel.Infinite
import LogOS.Kernel.UngradedKernel.Infinite.Lemmas as IKL

-- Capstone: approximation principle at the boundary.
--
-- For an infinite kernel, bounding `Th⋆` is equivalent to bounding every
-- finite approximant in the canonical ω-chain.

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (IK : InfiniteKernel Sig Q) where
  private
    module L = IKL.For IK
    open InfiniteKernel IK using (BB; ωCPO)
    CP = BulkBoundary.bnd BB
    module CP = ConPreorder CP

  approx≤Th⋆ : ∀ n → CP._⊑_ (L.approxS n) (L.Th⋆)
  approx≤Th⋆ n =
    let sup≤th = snd L.Th⋆-as-supω
        ub     = Truth.GuardedCore.OmegaCPO.ub ωCPO L.approxS n
    in CP.trans ub sup≤th

  Th⋆≤↔approxAll≤
    : (c : CP.Con)
    → (CP._⊑_ (L.Th⋆) c) ↔ (∀ n → CP._⊑_ (L.approxS n) c)
  Th⋆≤↔approxAll≤ c =
    record
      { to   = λ th≤c n → CP.trans (approx≤Th⋆ n) th≤c
      ; from = λ ub → L.approx-all→Th⋆≤ c ub
      }
