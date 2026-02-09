{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Training where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

import LogOS.Packs.Agents.Experimental.Learning.RGFlow as RGFlow
import LogOS.Packs.Agents.Experimental.Arguments.ScalingLaws as ScalingLaws

import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Ops as Ops
import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.KernelBridge as KB
import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Loss as Loss
import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Resources as Resources
import LogOS.Packs.Agents.Experimental.Arguments.LossStability as LossStability

-- Training-side story: connect loss-driven stability to kernel scaling bounds.

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

  module OpsFor = Ops.For K ωCPO
  module KBFor = KB.For K ωCPO
  module LossFor = Loss.For K ωCPO
  module ResFor = Resources.For K ωCPO

  open RG using (Policy; RGStep; RGStable; ScalingDimension; applyRG)
  open RG.μ using (_⊑_)
  open QAdapter Q using (Scale)
  open GradedKernel K using (Code; decode)

  module LS = LossStability.For K ωCPO
  open LS public using (LossOrderReflecting; lossDecrease-stable)

  record TransformerTrainingBridge (g : Scale) : Set (lsuc (lsuc ℓ)) where
    field
      bridge : KBFor.TransformerKernelBridge
      step : RGStep g
      dim : ScalingDimension step
      closed
        : ∀ {c}
          → KBFor.TransformerKernelBridge.IsTransformerPolicy bridge c
          → KBFor.TransformerKernelBridge.IsTransformerPolicy bridge (applyRG step c)
      trainParam : OpsFor.TransformerOps.Param (KBFor.TransformerKernelBridge.ops bridge)
                 → OpsFor.TransformerOps.Param (KBFor.TransformerKernelBridge.ops bridge)
      train-correct
        : ∀ p
          → KBFor.TransformerKernelBridge.encode bridge (trainParam p)
            ≡ applyRG step (KBFor.TransformerKernelBridge.encode bridge p)

  TrainingEndo : Scale → Set (lsuc ℓ)
  TrainingEndo g = RGStep g

  rgStepFromEndo
    : ∀ {g} → TrainingEndo g → RGStep g
  rgStepFromEndo A = A

  record LossObservable (ops : OpsFor.TransformerOps) : Set (lsuc (lsuc ℓ)) where
    field
      action : RG.ScaleAction
      obs : Policy → Scale
      mono : ∀ {c d} → _⊑_ c d → QAdapter._≤s_ Q (obs c) (obs d)
      scale : ∀ {g} (s : RGStep g) → ∀ c
            → QAdapter._≤s_ Q
                (obs (applyRG s c))
                (QAdapter._·_ Q (RG.ScaleAction.act action g) (obs c))

  record LossObservableFromData (B : KBFor.TransformerKernelBridge) : Set (lsuc (lsuc ℓ)) where
    private
      ops = KBFor.TransformerKernelBridge.ops B
    field
      lossData : LossFor.LossData ops
      action : RG.ScaleAction
      obs : Policy → Scale
      obs-encode
        : ∀ (p : OpsFor.TransformerOps.Param ops)
        → obs (KBFor.TransformerKernelBridge.encode B p)
          ≡ LossFor.lossParam lossData p
      mono : ∀ {c d} → _⊑_ c d → QAdapter._≤s_ Q (obs c) (obs d)
      scale : ∀ {g} (s : RGStep g) → ∀ c
            → QAdapter._≤s_ Q
                (obs (applyRG s c))
                (QAdapter._·_ Q (RG.ScaleAction.act action g) (obs c))

    asLossObservable : LossObservable ops
    asLossObservable =
      record
        { action = action
        ; obs = obs
        ; mono = mono
        ; scale = scale
        }

  -- Next-token loss made explicit as a LossObservableFromData.
  record NextTokenLossObservableFromData (B : KBFor.TransformerKernelBridge) : Set (lsuc (lsuc ℓ)) where
    private
      ops = KBFor.TransformerKernelBridge.ops B
    field
      lossData : LossFor.NextTokenLossData ops
      action : RG.ScaleAction
      obs : Policy → Scale
      obs-encode
        : ∀ (p : OpsFor.TransformerOps.Param ops)
        → obs (KBFor.TransformerKernelBridge.encode B p)
          ≡ LossFor.lossParam (LossFor.nextTokenLossData lossData) p
      mono : ∀ {c d} → _⊑_ c d → QAdapter._≤s_ Q (obs c) (obs d)
      scale : ∀ {g} (s : RGStep g) → ∀ c
            → QAdapter._≤s_ Q
                (obs (applyRG s c))
                (QAdapter._·_ Q (RG.ScaleAction.act action g) (obs c))

    asLossObservableFromData : LossObservableFromData B
    asLossObservableFromData =
      record
        { lossData = LossFor.nextTokenLossData lossData
        ; action = action
        ; obs = obs
        ; obs-encode = obs-encode
        ; mono = mono
        ; scale = scale
        }

    asLossObservable : LossObservable ops
    asLossObservable =
      LossObservableFromData.asLossObservable asLossObservableFromData

  scalingDimensionFromLoss
    : ∀ {g} {s : RGStep g} {ops} (L : LossObservable ops)
    → ScalingDimension s
  scalingDimensionFromLoss {s = s} L =
    record
      { action = LossObservable.action L
      ; obs = LossObservable.obs L
      ; mono = LossObservable.mono L
      ; scale = LossObservable.scale L s
      }

  record TrainingSpec (g : Scale) : Set (lsuc (lsuc ℓ)) where
    field
      bridge : KBFor.TransformerKernelBridge
      endo : TrainingEndo g
      lossObsData : LossObservableFromData bridge
      closed
        : ∀ {c}
          → KBFor.TransformerKernelBridge.IsTransformerPolicy bridge c
          → KBFor.TransformerKernelBridge.IsTransformerPolicy bridge
              (applyRG (rgStepFromEndo endo) c)
      trainParam : OpsFor.TransformerOps.Param (KBFor.TransformerKernelBridge.ops bridge)
                 → OpsFor.TransformerOps.Param (KBFor.TransformerKernelBridge.ops bridge)
      train-correct
        : ∀ p
          → KBFor.TransformerKernelBridge.encode bridge (trainParam p)
            ≡ applyRG (rgStepFromEndo endo) (KBFor.TransformerKernelBridge.encode bridge p)

    lossObs : LossObservable (KBFor.TransformerKernelBridge.ops bridge)
    lossObs = LossObservableFromData.asLossObservable lossObsData

  record OptimizerTraining (g : Scale) : Set (lsuc (lsuc ℓ)) where
    field
      spec : TrainingSpec g
      lossOrder : LossOrderReflecting
        (LossObservableFromData.obs (TrainingSpec.lossObsData spec))
      lossDecrease
        : ∀ p
        → QAdapter._≤s_ Q
            (LossFor.lossParam
              (LossObservableFromData.lossData (TrainingSpec.lossObsData spec))
              (TrainingSpec.trainParam spec p))
            (LossFor.lossParam
              (LossObservableFromData.lossData (TrainingSpec.lossObsData spec)) p)

  optimizer-policy-decrease
    : ∀ {g} (O : OptimizerTraining g)
    → ∀ p
    → QAdapter._≤s_ Q
        (LossObservableFromData.obs (TrainingSpec.lossObsData (OptimizerTraining.spec O))
          (applyRG (rgStepFromEndo (TrainingSpec.endo (OptimizerTraining.spec O)))
            (KBFor.TransformerKernelBridge.encode (TrainingSpec.bridge (OptimizerTraining.spec O)) p)))
        (LossObservableFromData.obs (TrainingSpec.lossObsData (OptimizerTraining.spec O))
          (KBFor.TransformerKernelBridge.encode (TrainingSpec.bridge (OptimizerTraining.spec O)) p))
  optimizer-policy-decrease O p =
    let open OptimizerTraining O
        S = spec
        B = TrainingSpec.bridge S
        L = TrainingSpec.lossObsData S
        lossD = LossObservableFromData.lossData L
        upd = TrainingSpec.trainParam S
        obs = LossObservableFromData.obs L
        obsUpd = LossObservableFromData.obs-encode L (upd p)
        obsP = LossObservableFromData.obs-encode L p
        step1 : QAdapter._≤s_ Q (obs (KBFor.TransformerKernelBridge.encode B (upd p)))
                               (LossFor.lossParam lossD p)
        step1 =
          subst
            (λ x → QAdapter._≤s_ Q x (LossFor.lossParam lossD p))
            (sym obsUpd)
            (lossDecrease p)
        step2 : QAdapter._≤s_ Q (obs (KBFor.TransformerKernelBridge.encode B (upd p)))
                               (obs (KBFor.TransformerKernelBridge.encode B p))
        step2 =
          subst
            (λ x → QAdapter._≤s_ Q (obs (KBFor.TransformerKernelBridge.encode B (upd p))) x)
            (sym obsP)
            step1
    in
    subst
      (λ x → QAdapter._≤s_ Q (obs x) (obs (KBFor.TransformerKernelBridge.encode B p)))
      (TrainingSpec.train-correct S p)
      step2

  optimizer-param-stable
    : ∀ {g} (O : OptimizerTraining g)
    → ∀ p
    → RGStable
        (rgStepFromEndo (TrainingSpec.endo (OptimizerTraining.spec O)))
        (KBFor.TransformerKernelBridge.encode (TrainingSpec.bridge (OptimizerTraining.spec O)) p)
  optimizer-param-stable O p =
    record
      { closed = LossOrderReflecting.reflect (OptimizerTraining.lossOrder O)
                  (optimizer-policy-decrease O p)
      }

  data OptimizerTag : Set where
    sgd : OptimizerTag
    adam : OptimizerTag

  record TaggedTraining (g : Scale) : Set (lsuc (lsuc ℓ)) where
    field
      optimizer : OptimizerTraining g
      tag : OptimizerTag

  record SGDTraining (g : Scale) : Set (lsuc (lsuc ℓ)) where
    field
      optimizer : OptimizerTraining g

  record AdamTraining (g : Scale) : Set (lsuc (lsuc ℓ)) where
    field
      optimizer : OptimizerTraining g

  tagged-from-sgd : ∀ {g} → SGDTraining g → TaggedTraining g
  tagged-from-sgd S =
    record
      { optimizer = SGDTraining.optimizer S
      ; tag = sgd
      }

  tagged-from-adam : ∀ {g} → AdamTraining g → TaggedTraining g
  tagged-from-adam A =
    record
      { optimizer = AdamTraining.optimizer A
      ; tag = adam
      }

  sgd-param-stable
    : ∀ {g} (S : SGDTraining g)
    → ∀ p
    → RGStable
        (rgStepFromEndo (TrainingSpec.endo (OptimizerTraining.spec (SGDTraining.optimizer S))))
        (KBFor.TransformerKernelBridge.encode
          (TrainingSpec.bridge (OptimizerTraining.spec (SGDTraining.optimizer S))) p)
  sgd-param-stable S = optimizer-param-stable (SGDTraining.optimizer S)

  adam-param-stable
    : ∀ {g} (A : AdamTraining g)
    → ∀ p
    → RGStable
        (rgStepFromEndo (TrainingSpec.endo (OptimizerTraining.spec (AdamTraining.optimizer A))))
        (KBFor.TransformerKernelBridge.encode
          (TrainingSpec.bridge (OptimizerTraining.spec (AdamTraining.optimizer A))) p)
  adam-param-stable A = optimizer-param-stable (AdamTraining.optimizer A)

  trainingBridgeFromSpec
    : ∀ {g} (S : TrainingSpec g)
    → TransformerTrainingBridge g
  trainingBridgeFromSpec S =
    record
      { bridge = TrainingSpec.bridge S
      ; step = rgStepFromEndo (TrainingSpec.endo S)
      ; dim = scalingDimensionFromLoss
                (LossObservableFromData.asLossObservable (TrainingSpec.lossObsData S))
      ; closed = TrainingSpec.closed S
      ; trainParam = TrainingSpec.trainParam S
      ; train-correct = TrainingSpec.train-correct S
      }

  trainingDynamicsFromSpec
    : ∀ {g} (S : TrainingSpec g)
    → KBFor.TF.TrainingDynamics (KBFor.coreFromBridge (TrainingSpec.bridge S)) g
  trainingDynamicsFromSpec S =
    record
      { step = rgStepFromEndo (TrainingSpec.endo S)
      ; dim = scalingDimensionFromLoss
                (LossObservableFromData.asLossObservable (TrainingSpec.lossObsData S))
      ; closed = TrainingSpec.closed S
      ; trainParam = TrainingSpec.trainParam S
      ; train-correct = TrainingSpec.train-correct S
      }

  trainingFromBridge
    : ∀ {g} (B : TransformerTrainingBridge g)
    → KBFor.TF.TrainingDynamics (KBFor.coreFromBridge (TransformerTrainingBridge.bridge B)) g
  trainingFromBridge B =
    record
      { step = TransformerTrainingBridge.step B
      ; dim = TransformerTrainingBridge.dim B
      ; closed = TransformerTrainingBridge.closed B
      ; trainParam = TransformerTrainingBridge.trainParam B
      ; train-correct = TransformerTrainingBridge.train-correct B
      }

  paramIsTransformer
    : ∀ {g} (B : TransformerTrainingBridge g)
    → (p : OpsFor.TransformerOps.Param (KBFor.TransformerKernelBridge.ops (TransformerTrainingBridge.bridge B)))
    → KBFor.TF.IsTransformerCode
        (KBFor.coreFromBridge (TransformerTrainingBridge.bridge B))
        (KBFor.TransformerKernelBridge.paramCode (TransformerTrainingBridge.bridge B) p)
  paramIsTransformer B p =
    let open KBFor.TransformerKernelBridge (TransformerTrainingBridge.bridge B) in
    subst IsTransformerPolicy (sym (paramCode-decode p)) (encode-is-transformer p)

  trainParam-code
    : ∀ {g} (B : TransformerTrainingBridge g)
    → (p : OpsFor.TransformerOps.Param (KBFor.TransformerKernelBridge.ops (TransformerTrainingBridge.bridge B)))
    → decode (KBFor.TransformerKernelBridge.paramCode (TransformerTrainingBridge.bridge B)
              (TransformerTrainingBridge.trainParam B p))
      ≡
      applyRG (TransformerTrainingBridge.step B)
        (decode (KBFor.TransformerKernelBridge.paramCode (TransformerTrainingBridge.bridge B) p))
  trainParam-code B p =
    let open KBFor.TransformerKernelBridge (TransformerTrainingBridge.bridge B) in
    let s = TransformerTrainingBridge.step B in
    trans
      (trans
        (paramCode-decode (TransformerTrainingBridge.trainParam B p))
        (TransformerTrainingBridge.train-correct B p))
      (cong (applyRG s) (sym (paramCode-decode p)))

  paramStable-scalingBound
    : ∀ {g} (B : TransformerTrainingBridge g)
    → (p : OpsFor.TransformerOps.Param (KBFor.TransformerKernelBridge.ops (TransformerTrainingBridge.bridge B)))
    → RGStable (TransformerTrainingBridge.step B)
        (KBFor.TransformerKernelBridge.encode (TransformerTrainingBridge.bridge B) p)
    → SL.ScalingBound (TransformerTrainingBridge.step B) (TransformerTrainingBridge.dim B)
        (KBFor.TransformerKernelBridge.paramCode (TransformerTrainingBridge.bridge B) p)
  paramStable-scalingBound B p st =
    let open KBFor.TransformerKernelBridge (TransformerTrainingBridge.bridge B) in
    let st' = KBFor.TF.stable-subst (sym (paramCode-decode p)) st in
    SL.scalingBound-from-stable
      (TransformerTrainingBridge.step B)
      (TransformerTrainingBridge.dim B)
      st'
