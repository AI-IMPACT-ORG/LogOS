{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.ObserverStepInvariance where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)

import LogOS.Kernel.LogicKernel as LK
import LogOS.Theorems.Meta.ObserverFromLogicKernel as ObsFrom
import LogOS.Theorems.Meta.GuardedTruthAt as GT

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : LK.LogicKernel Sig Q)
  where

  module O = ObsFrom.For K

  Truth⊤ : O.Code → Set
  Truth⊤ _ = ⊤

  -- Sanity: the canonical “compute then stabilise” observer step is equivalent
  -- (up to decode) to the raw operational presentation `FlowCode`.
  step-invariance
    : ∀ {γ}
    → O.Observable⋆ {ℓO = lzero} Truth⊤ γ
      ↔ O.Observable⋆-FlowCode {ℓO = lzero} Truth⊤ γ
  step-invariance = O.Observable⋆↔Observable⋆-FlowCode {ℓO = lzero} Truth⊤

  module G = GT.For K

  guarded-step-invariance
    : ∀ {w γ}
    → G.GuardedTruthAt {ℓO = lzero} w γ
      ↔ G.GuardedTruthAt-FlowCode {ℓO = lzero} w γ
  guarded-step-invariance {w} {γ} =
    G.GuardedTruthAt↔GuardedTruthAt-FlowCode {ℓO = lzero} w {γ = γ}
