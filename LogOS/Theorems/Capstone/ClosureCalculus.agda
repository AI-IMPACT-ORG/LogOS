{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Capstone.ClosureCalculus where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel.Endo
open import LogOS.Kernel.UngradedKernel.Infinite
import LogOS.Kernel.UngradedKernel.Infinite.Lemmas as IKL

-- Capstone: closure steps form a compositional “calculus” and all fix `Th⋆`.
-- A closure step is any endomap f with `id ≤ f ≤ Flow`.

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (IK : InfiniteKernel Sig Q) where
  private
    module L = IKL.For IK

  open L public using (step-fixed-at-Th⋆)
