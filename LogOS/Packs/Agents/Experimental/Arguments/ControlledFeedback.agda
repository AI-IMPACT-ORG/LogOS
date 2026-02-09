{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.ControlledFeedback where

open import LogOS.Prelude
open import LogOS.Prelude using (_×_; snd)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

import LogOS.Packs.Agents.Experimental.Learning.RGFlow as RGFlow
import LogOS.Packs.Agents.Experimental.Arguments.ScalingLaws as ScalingLaws
import LogOS.Packs.Agents.Experimental.Arguments.TransformerScaling as TransformerScaling
import LogOS.Packs.Agents.Experimental.Arguments.Context as Ctx

-- LogOS-native core for budgeted controlled feedback systems.
--
-- A concrete architecture (e.g. transformer, state-space model, controller stack)
-- is modeled as a policy family plus RG-compatible training dynamics.

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
  module TS = TransformerScaling.For K ωCPO

  open RG using (Policy; RGStep; RGStable; RGFixed; ScalingDimension; applyRG; rg-μ; rg-μ-fixed)
  open QAdapter Q using (Scale)
  open GradedKernel K using (Code; decode)

  record ControlledFeedbackCore : Set (lsuc (lsuc ℓ)) where
    field
      Param : Set ℓ
      encode : Param → Policy
      IsControlledPolicy : Policy → Set ℓ
      encode-is-controlled : ∀ p → IsControlledPolicy (encode p)

  open ControlledFeedbackCore public

  IsControlledCode : ControlledFeedbackCore → Code → Set ℓ
  IsControlledCode C γ = IsControlledPolicy C (decode γ)

  record ControlledDynamics (C : ControlledFeedbackCore) (g : Scale) : Set (lsuc (lsuc ℓ)) where
    field
      step : RGStep g
      dim  : ScalingDimension step
      closed
        : ∀ {c} → IsControlledPolicy C c → IsControlledPolicy C (applyRG step c)
      trainParam : Param C → Param C
      train-correct : ∀ p → encode C (trainParam p) ≡ applyRG step (encode C p)

  open ControlledDynamics public

  stable-subst
    : ∀ {g} {s : RGStep g} {c d : Policy}
    → c ≡ d
    → RGStable s c
    → RGStable s d
  stable-subst {s = s} eq st = subst (RGStable s) eq st

  IsTrainedStable
    : ∀ {g} (C : ControlledFeedbackCore) (D : ControlledDynamics C g)
    → Code → Set ℓ
  IsTrainedStable C D γ =
    IsControlledCode C γ
    × RGStable (step D) (decode γ)

  record ConvergesToMu {g : Scale} (C : ControlledFeedbackCore) (D : ControlledDynamics C g)
    : Set (lsuc (lsuc ℓ)) where
    field
      scott : RG.μ.ScottContinuous (applyRG (step D))

  open ConvergesToMu public

  mu-stable
    : ∀ {g} {C : ControlledFeedbackCore} {D : ControlledDynamics C g}
    → ConvergesToMu C D
    → RGStable (step D) (rg-μ (step D))
  mu-stable {D = D} conv =
    let fixed = rg-μ-fixed (step D) (scott conv) in
    record { closed = RGFixed.le fixed }

  IsTrainedMu
    : ∀ {g} (C : ControlledFeedbackCore) (D : ControlledDynamics C g)
    → Code → Set ℓ
  IsTrainedMu C D γ =
    IsControlledCode C γ
    × decode γ ≡ rg-μ (step D)

  trainedMu→trainedStable
    : ∀ {g} {C : ControlledFeedbackCore} {D : ControlledDynamics C g}
    → ConvergesToMu C D
    → ∀ {γ} → IsTrainedMu C D γ → IsTrainedStable C D γ
  trainedMu→trainedStable conv {γ} (ctl , eq) =
    ctl , stable-subst (sym eq) (mu-stable conv)

  toTrainingStable
    : ∀ {g} (C : ControlledFeedbackCore) (D : ControlledDynamics C g)
    → TS.TransformerTraining g
  toTrainingStable C D =
    record
      { IsTransformer = IsTrainedStable C D
      ; step = step D
      ; dim = dim D
      ; stable = λ {γ} st → snd st
      }

  toTrainingMu
    : ∀ {g} (C : ControlledFeedbackCore) (D : ControlledDynamics C g)
    → ConvergesToMu C D
    → TS.TransformerTraining g
  toTrainingMu C D conv =
    record
      { IsTransformer = IsTrainedMu C D
      ; step = step D
      ; dim = dim D
      ; stable = λ {γ} st → snd (trainedMu→trainedStable conv st)
      }

  trained-scalingBound
    : ∀ {g} (C : ControlledFeedbackCore) (D : ControlledDynamics C g) {γ}
    → IsTrainedStable C D γ
    → SL.ScalingBound (step D) (dim D) γ
  trained-scalingBound C D st =
    SL.scalingBound-from-stable (step D) (dim D) (snd st)

  trainedMu-scalingBound
    : ∀ {g} (C : ControlledFeedbackCore) (D : ControlledDynamics C g)
    → ConvergesToMu C D
    → ∀ {γ} → IsTrainedMu C D γ
    → SL.ScalingBound (step D) (dim D) γ
  trainedMu-scalingBound C D conv st =
    trained-scalingBound C D (trainedMu→trainedStable conv st)

-- Context-bundled entrypoint (convenience).
module ForCtx
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (C : Ctx.Context Sig Q)
  where
  open For (Ctx.Context.K C) (Ctx.Context.ωCPO C) public
