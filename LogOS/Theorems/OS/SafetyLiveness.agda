{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.OS.SafetyLiveness where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Kernel.Infinite
import LogOS.Kernel.Infinite.Lemmas as IKL

-- OS-style “safety/liveness at the limit” wrapper:
-- stable predicates (upward closed + ω-sup closed) hold at the global limit `Th⋆`
-- whenever they hold on all finite approximants.
--
-- This is exactly the standard “prove safety on finite executions, conclude for
-- the limit semantics” principle, stated in LogOS-native terms.

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (IK : InfiniteKernel Sig Q) where
  private
    module L = IKL.For IK

  SafetyPredicate = L.StablePredicate
  safety-on-approximants→safety-on-limit = L.stable-on-approximants→stable-on-Th⋆
