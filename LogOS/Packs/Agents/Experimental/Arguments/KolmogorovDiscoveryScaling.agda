{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.KolmogorovDiscoveryScaling where

open import LogOS.Prelude

open import Data.Nat using (ℕ)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)
import LogOS.Packs.Agents.Experimental.Learning.RGFlow as RGFlow
import LogOS.Packs.Agents.Experimental.Arguments.ScalingLaws as ScalingLaws
import LogOS.Packs.Agents.Experimental.Arguments.KolmogorovOptimality as KOpt

-- Kolmogorov-optimal discovery, publicised via self-reference (Pr).
-- This prevents "assuming the answer": discovery is the maximal admissible,
-- decode-extensional, Flow-stable fragment of KOptimal.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  open GradedKernel K using (Code; decode)
  open QAdapter Q using (_≤s_; Scale)

  module KO = KOpt.For K
  open KO public using (Dec; KOptimal)
  module Obs = KO.Obs

  module RG = RGFlow.For K ωCPO
  module SL = ScalingLaws.For K ωCPO

  open RG using (RGStep; RGStable; ScalingDimension)

  -- Scaling consequence, if discovery is known to imply RG stability.
  record DiscoveryScaling {g : Scale} (s : RGStep g) : Set (lsuc (lsuc ℓ)) where
    field
      size : Code → ℕ
      dim  : ScalingDimension s
      stable : ∀ {γ} → Obs.DiscoverCode size γ → RGStable s (decode γ)

  open DiscoveryScaling public

  discovery-scalingBound
    : ∀ {g} {s : RGStep g} (A : DiscoveryScaling s) {γ}
    → Obs.DiscoverCode (size A) γ
    → SL.ScalingBound s (dim A) γ
  discovery-scalingBound {s = s} A d =
    SL.scalingBound-from-stable s (dim A) (stable A d)
