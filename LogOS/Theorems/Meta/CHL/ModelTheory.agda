{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.ModelTheory where

-- Model-theory view: refinement implies semantic entailment at the H/boundary tiers.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel hiding (Box; decode-Box; box-mono)
import LogOS.Theorems.Meta.CHL.Core as CHL
import LogOS.Theorems.Meta.CHL.Completeness as Complete

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where

  module C = CHL.For K
  open C
  module Co = Complete.For K

  module HT = Truth.HomotypicalTruth Sig Q (Kernel.HWorld K)

  -- Refinement implies H-tier entailment.
  entails-H
    : ∀ {gamma delta}
    → Refines gamma delta
    → ∀ (w : LogOSSignature.Cosp Sig)
    → HT.HLayer.Sat_H (Kernel.HTruth K) w (denote gamma)
    → HT.HLayer.Sat_H (Kernel.HTruth K) w (denote delta)
  entails-H le _ sat =
    HT.HLayer.mono-Con (Kernel.HTruth K) le sat

  -- Refinement implies boundary entailment (via sat-coh).
  entails-boundary
    : ∀ {gamma delta}
    → Refines gamma delta
    → Co.Entails∂ gamma delta
  entails-boundary = Co.sound∂
