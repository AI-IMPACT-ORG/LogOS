{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.LearningScaling where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)
open import LogOS.Kernel.Graded.ToKernel as ToKernel
open import LogOS.Kernel as Kernel
import LogOS.Kernel.Core as KCore

import LogOS.Packs.Agents.Experimental.Learning.RGFlow as RGFlow
import LogOS.Packs.Agents.Experimental.Arguments.ScalingLaws as ScalingLaws
import LogOS.Theorems.Meta.LimitPublicisation as LP

-- Generic learning vs scaling-law bridge: RG steps + scaling dimensions.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module RG = RGFlow.For K ωCPO
  module SL = ScalingLaws.For K ωCPO

  open RG using (RGStep; RGStable; ScalingDimension; rg-iter)
  open SL using (ScalingBound; scalingBound-from-stable; scalingBound-reify; scaling-law)
  open QAdapter Q using (Scale)
  open GradedKernel K using (Code; decode; reify)

  record LearningTraining (g : Scale) : Set (lsuc (lsuc ℓ)) where
    field
      IsLearned : Code → Set ℓ
      step : RGStep g
      dim  : ScalingDimension step
      stable : ∀ {γ} → IsLearned γ → RGStable step (decode γ)

  open LearningTraining public

  -- Main consequence: learned codes at RG-stable policies obey the bound.
  learning-scalingBound
    : ∀ {g} (T : LearningTraining g) {γ}
    → IsLearned T γ
    → ScalingBound (step T) (dim T) γ
  learning-scalingBound T tf =
    scalingBound-from-stable (step T) (dim T) (stable T tf)

  -- Iterated scaling law for the training RG step.
  learning-scaling-iter
    : ∀ {g} (T : LearningTraining g) n
    → QAdapter._≤s_ Q
        (ScalingDimension.obs (dim T) (rg-iter (step T) n))
        (QAdapter._·_ Q
          (RG.scalePow n (RG.ScaleAction.act (ScalingDimension.action (dim T)) g))
          (ScalingDimension.obs (dim T) (rg-iter (step T) zero)))
  learning-scaling-iter T = scaling-law (dim T)

  -- Reflection closure: scaling bounds are invariant under reify.
  learning-scalingBound-reify
    : ∀ {g} (T : LearningTraining g) γ
    → ScalingBound (step T) (dim T) (reify γ)
      ↔
      ScalingBound (step T) (dim T) γ
  learning-scalingBound-reify T γ =
    scalingBound-reify {s = step T} {D = dim T} γ

  -- Optional: publicise scaling bounds when step-grade = sat.
  module Public
    {stepSat : ToKernel.StepIsSat K}
    {bm : KCore.BodyMonotoneShape (GradedKernel.shape K)}
    where

    module SLPublic = SL.Public {stepSat = stepSat} {bm = bm}
    open SLPublic public

    learning-scalingBound-public
      : ∀ {g} (T : LearningTraining g)
      → (stableBound : ∀ γ →
          ScalingBoundK (step T) (dim T) γ
          ↔
          ScalingBoundK (step T) (dim T) (Kernel.FlowCode K₀ γ))
      → ∀ {γ}
      → ScalingBoundK (step T) (dim T) γ
      → LP.LimitPublicisation K₀ (ScalingBoundK (step T) (dim T)) γ
    learning-scalingBound-public T stableBound =
      scalingBound-public (step T) (dim T) stableBound
