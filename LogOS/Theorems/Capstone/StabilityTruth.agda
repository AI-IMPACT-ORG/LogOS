{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Capstone.StabilityTruth where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel.Infinite
import LogOS.Kernel.Infinite.Lemmas as IKL

-- Capstone: stable properties reflect from finite approximants to global truth.
--
-- This is the clean “stability = truth at the limit” schema:
-- once a predicate is upward closed and ω-sup closed, it holds at `Th⋆`
-- whenever it holds on all finite approximants.

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (IK : InfiniteKernel Sig Q) where
  private
    module L = IKL.For IK

  open L public using (StablePredicate; stable-on-approximants→stable-on-Th⋆)
