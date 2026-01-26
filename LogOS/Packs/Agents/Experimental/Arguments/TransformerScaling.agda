{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerScaling where

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
import LogOS.Packs.Agents.Experimental.Arguments.LearningScaling as LearningScaling
import LogOS.Packs.Agents.Experimental.Arguments.ScalingLaws as ScalingLaws
import LogOS.Theorems.Meta.LimitPublicisation as LP

-- Transformer scaling argument (minimal assumptions, reflection-closed):
-- if transformer training is an RG step with a scaling dimension,
-- scaling laws follow from the kernel.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module RG = RGFlow.For K ωCPO
  module LS = LearningScaling.For K ωCPO
  module SL = ScalingLaws.For K ωCPO

  open RG using (RGStep; RGStable; ScalingDimension; rg-iter)
  open SL using (ScalingBound)
  open QAdapter Q using (Scale)
  open GradedKernel K using (Code; decode; reify)

  -- Minimal transformer training package: a predicate on codes plus an RG step.
  record TransformerTraining (g : Scale) : Set (lsuc (lsuc ℓ)) where
    field
      IsTransformer : Code → Set ℓ
      step : RGStep g
      dim  : ScalingDimension step
      stable : ∀ {γ} → IsTransformer γ → RGStable step (decode γ)

  open TransformerTraining public

  toLearning : ∀ {g} → TransformerTraining g → LS.LearningTraining g
  toLearning T =
    record
      { IsLearned = IsTransformer T
      ; step = step T
      ; dim = dim T
      ; stable = stable T
      }

  -- Main consequence: transformer codes at RG-stable policies obey the bound.
  transformer-scalingBound
    : ∀ {g} (T : TransformerTraining g) {γ}
    → IsTransformer T γ
    → ScalingBound (step T) (dim T) γ
  transformer-scalingBound T tf =
    LS.learning-scalingBound (toLearning T) tf

  -- Iterated scaling law for the training RG step.
  transformer-scaling-iter
    : ∀ {g} (T : TransformerTraining g) n
    → QAdapter._≤s_ Q
        (ScalingDimension.obs (dim T) (rg-iter (step T) n))
        (QAdapter._·_ Q
          (RG.scalePow n (RG.ScaleAction.act (ScalingDimension.action (dim T)) g))
          (ScalingDimension.obs (dim T) (rg-iter (step T) zero)))
  transformer-scaling-iter T = LS.learning-scaling-iter (toLearning T)

  -- Reflection closure: scaling bounds are invariant under reify.
  transformer-scalingBound-reify
    : ∀ {g} (T : TransformerTraining g) γ
    → ScalingBound (step T) (dim T) (reify γ)
      ↔
      ScalingBound (step T) (dim T) γ
  transformer-scalingBound-reify T γ =
    LS.learning-scalingBound-reify (toLearning T) γ

  -- Optional: publicise scaling bounds when step-grade = sat.
  module Public
    {stepSat : ToKernel.StepIsSat K}
    {bm : KCore.BodyMonotoneShape (GradedKernel.shape K)}
    where

    module LSPublic = LS.Public {stepSat = stepSat} {bm = bm}

    transformer-scalingBound-public
      : ∀ {g} (T : TransformerTraining g)
      → (stableBoundBoxBody : ∀ γ →
          LSPublic.ScalingBoundK (step T) (dim T) γ
          ↔
          LSPublic.ScalingBoundK (step T) (dim T)
            (Kernel.Box LSPublic.K₀ (Kernel.Body LSPublic.K₀ γ)))
      → ∀ {γ}
      → LSPublic.ScalingBoundK (step T) (dim T) γ
      → LP.LimitPublicisation LSPublic.K₀ (LSPublic.ScalingBoundK (step T) (dim T)) γ
    transformer-scalingBound-public T stableBoundBoxBody =
      LSPublic.learning-scalingBound-public (toLearning T) stableBoundBoxBody
