{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerFormalization where

open import LogOS.Prelude

open import LogOS.Prelude.List using (List)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

import LogOS.Packs.Agents.Experimental.Learning.RGFlow as RGFlow
import LogOS.Packs.Agents.Experimental.Arguments.ScalingLaws as ScalingLaws
import LogOS.Packs.Agents.Experimental.Arguments.TransformerScaling as TransformerScaling
import LogOS.Packs.Agents.Experimental.Arguments.ControlledFeedback as ControlledFeedback
import LogOS.Packs.Agents.Experimental.Arguments.Context as Ctx

-- Compatibility layer:
-- - keeps the transformer-facing names used by existing modules/docs;
-- - delegates training/scaling semantics to the ControlledFeedback core.
--
-- This keeps “transformer” as an architecture instance of a smaller
-- LogOS-native controlled-feedback interface.

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
  module CF = ControlledFeedback.For K ωCPO

  open RG using (Policy; RGStep; RGStable; ScalingDimension; applyRG; rg-μ)
  open QAdapter Q using (Scale)
  open GradedKernel K using (Code; decode)

  -- Transformer core: token-level interface + parameterization as policies.
  record TransformerCore : Set (lsuc (lsuc ℓ)) where
    field
      Token : Set ℓ
      Param : Set ℓ

      -- Standard transformer interface: sequence-to-sequence map.
      forward : Param → List Token → List Token

      -- Kernel-native view: parameters map to boundary policies.
      encode : Param → Policy

      -- Architectural predicate on policies (for structural constraints).
      IsTransformerPolicy : Policy → Set ℓ
      encode-is-transformer : ∀ p → IsTransformerPolicy (encode p)

  open TransformerCore public

  toControlledCore : TransformerCore → CF.ControlledFeedbackCore
  toControlledCore T =
    record
      { Param = Param T
      ; encode = encode T
      ; IsControlledPolicy = IsTransformerPolicy T
      ; encode-is-controlled = encode-is-transformer T
      }

  IsTransformerCode : TransformerCore → Code → Set ℓ
  IsTransformerCode T γ = CF.IsControlledCode (toControlledCore T) γ

  -- Architecture-specific training metadata; semantics are delegated to
  -- ControlledFeedback via `toControlledDynamics`.
  record TrainingDynamics (T : TransformerCore) (g : Scale) : Set (lsuc (lsuc ℓ)) where
    field
      step : RGStep g
      dim  : ScalingDimension step

      -- Closed under training: transformer policies stay transformer policies.
      closed
        : ∀ {c} → IsTransformerPolicy T c → IsTransformerPolicy T (applyRG step c)

      -- Parameter update semantics (concrete enough to represent SGD-like steps).
      trainParam : Param T → Param T
      train-correct : ∀ p → encode T (trainParam p) ≡ applyRG step (encode T p)

  open TrainingDynamics public

  toControlledDynamics
    : ∀ {g} {T : TransformerCore}
    → TrainingDynamics T g
    → CF.ControlledDynamics (toControlledCore T) g
  toControlledDynamics D =
    record
      { step = step D
      ; dim = dim D
      ; closed = closed D
      ; trainParam = trainParam D
      ; train-correct = train-correct D
      }

  -- Stability transport along propositional equality (`≡`).
  stable-subst
    : ∀ {g} {s : RGStep g} {c d : Policy}
    → c ≡ d
    → RGStable s c
    → RGStable s d
  stable-subst = CF.stable-subst

  -- Trained transformers as RG-stable policies (most general statement).
  IsTrainedStable : ∀ {g} (T : TransformerCore) (D : TrainingDynamics T g) → Code → Set ℓ
  IsTrainedStable T D γ =
    CF.IsTrainedStable (toControlledCore T) (toControlledDynamics D) γ

  -- Convergence to the μ-fixed point (derivable when Scott-continuity holds).
  record ConvergesToMu {g : Scale} (T : TransformerCore) (D : TrainingDynamics T g)
    : Set (lsuc (lsuc ℓ)) where
    field
      scott : RG.μ.ScottContinuous (applyRG (step D))

  open ConvergesToMu public

  toControlledConverges
    : ∀ {g} {T : TransformerCore} {D : TrainingDynamics T g}
    → ConvergesToMu T D
    → CF.ConvergesToMu (toControlledCore T) (toControlledDynamics D)
  toControlledConverges conv =
    record { scott = ConvergesToMu.scott conv }

  mu-stable
    : ∀ {g} {T : TransformerCore} {D : TrainingDynamics T g}
    → ConvergesToMu T D
    → RGStable (step D) (rg-μ (step D))
  mu-stable {T = T} {D = D} conv =
    CF.mu-stable (toControlledConverges {T = T} {D = D} conv)

  IsTrainedMu : ∀ {g} (T : TransformerCore) (D : TrainingDynamics T g) → Code → Set ℓ
  IsTrainedMu T D γ =
    CF.IsTrainedMu (toControlledCore T) (toControlledDynamics D) γ

  trainedMu→trainedStable
    : ∀ {g} {T : TransformerCore} {D : TrainingDynamics T g}
    → ConvergesToMu T D
    → ∀ {γ} → IsTrainedMu T D γ → IsTrainedStable T D γ
  trainedMu→trainedStable {T = T} {D = D} conv =
    CF.trainedMu→trainedStable
      (toControlledConverges {T = T} {D = D} conv)

  -- Canonical TransformerTraining instance for trained transformers.
  toTrainingStable
    : ∀ {g} (T : TransformerCore) (D : TrainingDynamics T g)
    → TS.TransformerTraining g
  toTrainingStable T D =
    CF.toTrainingStable (toControlledCore T) (toControlledDynamics D)

  toTrainingMu
    : ∀ {g} (T : TransformerCore) (D : TrainingDynamics T g)
    → ConvergesToMu T D
    → TS.TransformerTraining g
  toTrainingMu T D conv =
    CF.toTrainingMu (toControlledCore T) (toControlledDynamics D)
      (toControlledConverges conv)

  -- Scaling bounds for trained transformers (stable-route).
  trained-scalingBound
    : ∀ {g} (T : TransformerCore) (D : TrainingDynamics T g) {γ}
    → IsTrainedStable T D γ
    → SL.ScalingBound (step D) (dim D) γ
  trained-scalingBound T D st =
    CF.trained-scalingBound (toControlledCore T) (toControlledDynamics D) st

  -- Scaling bounds for μ-trained transformers (convergence-route).
  trainedMu-scalingBound
    : ∀ {g} (T : TransformerCore) (D : TrainingDynamics T g)
    → ConvergesToMu T D
    → ∀ {γ} → IsTrainedMu T D γ
    → SL.ScalingBound (step D) (dim D) γ
  trainedMu-scalingBound T D conv st =
    CF.trainedMu-scalingBound (toControlledCore T) (toControlledDynamics D)
      (toControlledConverges conv) st

-- Context-bundled entrypoint (convenience).
module ForCtx
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (C : Ctx.Context Sig Q)
  where
  open For (Ctx.Context.K C) (Ctx.Context.ωCPO C) public
