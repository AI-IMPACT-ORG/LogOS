{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerFormalization where

open import LogOS.Prelude

open import Data.List using (List)
open import Data.Product using (_×_; snd)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

import LogOS.Packs.Agents.Experimental.Learning.RGFlow as RGFlow
import LogOS.Packs.Agents.Experimental.Arguments.ScalingLaws as ScalingLaws
import LogOS.Packs.Agents.Experimental.Arguments.TransformerScaling as TransformerScaling

-- Transformer formalization: enough structure to match real transformers
-- (tokens, sequences, parameters, forward pass) while staying kernel-native.

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

  IsTransformerCode : TransformerCore → Code → Set ℓ
  IsTransformerCode T γ = IsTransformerPolicy T (decode γ)

  -- Training dynamics as an RG step with a scaling dimension.
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

  -- Stability transport along definitional equality.
  stable-subst
    : ∀ {g} {s : RGStep g} {c d : Policy}
    → c ≡ d
    → RGStable s c
    → RGStable s d
  stable-subst {s = s} eq st = subst (RGStable s) eq st

  -- Trained transformers as RG-stable policies (most general statement).
  IsTrainedStable : ∀ {g} (T : TransformerCore) (D : TrainingDynamics T g) → Code → Set ℓ
  IsTrainedStable T D γ =
    IsTransformerCode T γ
    × RGStable (step D) (decode γ)

  -- Convergence to the μ-fixed point (derivable when Scott-continuity holds).
  record ConvergesToMu {g : Scale} (T : TransformerCore) (D : TrainingDynamics T g)
    : Set (lsuc (lsuc ℓ)) where
    field
      scott : RG.μ.ScottContinuous (applyRG (step D))

  open ConvergesToMu public

  mu-stable
    : ∀ {g} {T : TransformerCore} {D : TrainingDynamics T g}
    → ConvergesToMu T D
    → RGStable (step D) (rg-μ (step D))
  mu-stable {D = D} conv =
    let fixed = rg-μ-fixed (step D) (scott conv) in
    record { closed = RGFixed.le fixed }

  IsTrainedMu : ∀ {g} (T : TransformerCore) (D : TrainingDynamics T g) → Code → Set ℓ
  IsTrainedMu T D γ =
    IsTransformerCode T γ
    × decode γ ≡ rg-μ (step D)

  trainedMu→trainedStable
    : ∀ {g} {T : TransformerCore} {D : TrainingDynamics T g}
    → ConvergesToMu T D
    → ∀ {γ} → IsTrainedMu T D γ → IsTrainedStable T D γ
  trainedMu→trainedStable conv {γ} (tf , eq) =
    tf , stable-subst (sym eq) (mu-stable conv)

  -- Canonical TransformerTraining instance for trained transformers.
  toTrainingStable
    : ∀ {g} (T : TransformerCore) (D : TrainingDynamics T g)
    → TS.TransformerTraining g
  toTrainingStable T D =
    record
      { IsTransformer = IsTrainedStable T D
      ; step = step D
      ; dim = dim D
      ; stable = λ {γ} st → snd st
      }

  toTrainingMu
    : ∀ {g} (T : TransformerCore) (D : TrainingDynamics T g)
    → ConvergesToMu T D
    → TS.TransformerTraining g
  toTrainingMu T D conv =
    record
      { IsTransformer = IsTrainedMu T D
      ; step = step D
      ; dim = dim D
      ; stable = λ {γ} st → snd (trainedMu→trainedStable conv st)
      }

  -- Scaling bounds for trained transformers (stable-route).
  trained-scalingBound
    : ∀ {g} (T : TransformerCore) (D : TrainingDynamics T g) {γ}
    → IsTrainedStable T D γ
    → SL.ScalingBound (step D) (dim D) γ
  trained-scalingBound T D st =
    SL.scalingBound-from-stable (step D) (dim D) (snd st)

  -- Scaling bounds for μ-trained transformers (convergence-route).
  trainedMu-scalingBound
    : ∀ {g} (T : TransformerCore) (D : TrainingDynamics T g)
    → ConvergesToMu T D
    → ∀ {γ} → IsTrainedMu T D γ
    → SL.ScalingBound (step D) (dim D) γ
  trainedMu-scalingBound T D conv st =
    trained-scalingBound T D (trainedMu→trainedStable conv st)
