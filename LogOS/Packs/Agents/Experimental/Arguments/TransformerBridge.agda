{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge where

open import LogOS.Prelude

open import LogOS.Prelude.List using (List; []; _∷_; map; zipWith)
open import LogOS.Prelude.Nat using (ℕ; zero; suc; _+_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

import LogOS.Packs.Agents.Experimental.Learning.RGFlow as RGFlow
import LogOS.Packs.Agents.Experimental.Arguments.ScalingLaws as ScalingLaws
import LogOS.Packs.Agents.Experimental.Arguments.TransformerFormalization as TransformerFormalization

-- Bridge from concrete transformer structure to kernel-native training/scaling.

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
  module TF = TransformerFormalization.For K ωCPO

  open RG using (Policy; RGStep; RGStable; ScalingDimension; applyRG)
  open RG.μ using (_⊑_)
  open QAdapter Q using (Scale)
  open GradedKernel K using (Code; decode; encode; decode∘encode)

  record TransformerOps : Set (lsuc (lsuc ℓ)) where
    field
      Token : Set ℓ
      Scalar : Set ℓ
      Vec : Set ℓ
      Param : Set ℓ
      LayerParam : Set ℓ
      HeadParam : Set ℓ

      layers : Param → List LayerParam
      heads : LayerParam → List HeadParam

      embed : Param → Token → Vec
      positional : Param → ℕ → Vec
      readout : Param → Vec → Token

      addV : Vec → Vec → Vec
      lnAttn : LayerParam → Vec → Vec
      lnFfn : LayerParam → Vec → Vec

      qProj : HeadParam → Vec → Vec
      kProj : HeadParam → Vec → Vec
      vProj : HeadParam → Vec → Vec
      oProj : LayerParam → Vec → Vec
      ffn : LayerParam → Vec → Vec

      dot : Vec → Vec → Scalar
      scaleV : Scalar → Vec → Vec
      softmax : List Scalar → List Scalar
      sumV : List Vec → Vec
      mergeHeadsSeq : List (List Vec) → List Vec

  mapWithIndex : ∀ {A B : Set ℓ} → (ℕ → A → B) → List A → List B
  mapWithIndex {A = A} {B = B} f = go zero
    where
      go : ℕ → List A → List B
      go _ [] = []
      go i (x ∷ xs) = f i x ∷ go (suc i) xs

  withPos : ∀ (ops : TransformerOps) → TransformerOps.Param ops → List (TransformerOps.Token ops)
          → List (TransformerOps.Vec ops)
  withPos ops p toks =
    let open TransformerOps ops in
    mapWithIndex (λ i t → addV (embed p t) (positional p i)) toks

  scores : ∀ (ops : TransformerOps)
         → TransformerOps.Vec ops
         → List (TransformerOps.Vec ops)
         → List (TransformerOps.Scalar ops)
  scores ops q ks =
    let open TransformerOps ops in
    map (dot q) ks

  weights : ∀ (ops : TransformerOps)
          → TransformerOps.Vec ops
          → List (TransformerOps.Vec ops)
          → List (TransformerOps.Scalar ops)
  weights ops q ks =
    let open TransformerOps ops in
    softmax (scores ops q ks)

  attend : ∀ (ops : TransformerOps)
         → TransformerOps.Vec ops
         → List (TransformerOps.Vec ops)
         → List (TransformerOps.Vec ops)
         → TransformerOps.Vec ops
  attend ops q ks vs =
    let open TransformerOps ops in
    sumV (zipWith scaleV (weights ops q ks) vs)

  headAttention : ∀ (ops : TransformerOps)
                → TransformerOps.HeadParam ops
                → List (TransformerOps.Vec ops)
                → List (TransformerOps.Vec ops)
  headAttention ops h seq =
    let open TransformerOps ops in
    let qs = map (qProj h) seq
        ks = map (kProj h) seq
        vs = map (vProj h) seq
    in map (λ q → attend ops q ks vs) qs

  multiHead : ∀ (ops : TransformerOps)
            → TransformerOps.LayerParam ops
            → List (TransformerOps.Vec ops)
            → List (TransformerOps.Vec ops)
  multiHead ops layer seq =
    let open TransformerOps ops in
    let hs = heads layer
        outs = map (λ h → headAttention ops h seq) hs
    in map (oProj layer) (mergeHeadsSeq outs)

  block : ∀ (ops : TransformerOps)
        → TransformerOps.LayerParam ops
        → List (TransformerOps.Vec ops)
        → List (TransformerOps.Vec ops)
  block ops layer seq =
    let open TransformerOps ops in
    let att = multiHead ops layer seq
        seq1 = map (lnAttn layer) (zipWith addV seq att)
        ffnOut = map (ffn layer) seq1
    in map (lnFfn layer) (zipWith addV seq1 ffnOut)

  applyLayers : ∀ (ops : TransformerOps)
              → List (TransformerOps.LayerParam ops)
              → List (TransformerOps.Vec ops)
              → List (TransformerOps.Vec ops)
  applyLayers ops [] seq = seq
  applyLayers ops (l ∷ ls) seq = applyLayers ops ls (block ops l seq)

  forwardOps : ∀ (ops : TransformerOps)
             → TransformerOps.Param ops
             → List (TransformerOps.Token ops)
             → List (TransformerOps.Token ops)
  forwardOps ops p toks =
    let open TransformerOps ops in
    let seq0 = withPos ops p toks
        seqN = applyLayers ops (layers p) seq0
    in map (readout p) seqN

  record TransformerKernelBridge : Set (lsuc (lsuc ℓ)) where
    field
      ops : TransformerOps
      encode : TransformerOps.Param ops → Policy
      IsTransformerPolicy : Policy → Set ℓ
      encode-is-transformer : ∀ p → IsTransformerPolicy (encode p)
      paramCode : TransformerOps.Param ops → Code
      paramCode-decode : ∀ p → decode (paramCode p) ≡ encode p

  module CanonicalEncoding
    (ops : TransformerOps)
    (encodeParam : TransformerOps.Param ops → Policy)
    (IsTransformerPolicy : Policy → Set ℓ)
    (encode-is-transformer : ∀ p → IsTransformerPolicy (encodeParam p))
    where

    paramCode : TransformerOps.Param ops → Code
    paramCode p = encode (encodeParam p)

    paramCode-decode : ∀ p → decode (paramCode p) ≡ encodeParam p
    paramCode-decode p = decode∘encode (encodeParam p)

    bridge : TransformerKernelBridge
    bridge =
      record
        { ops = ops
        ; encode = encodeParam
        ; IsTransformerPolicy = IsTransformerPolicy
        ; encode-is-transformer = encode-is-transformer
        ; paramCode = paramCode
        ; paramCode-decode = paramCode-decode
        }

  coreFromBridge : TransformerKernelBridge → TF.TransformerCore
  coreFromBridge B =
    let ops = TransformerKernelBridge.ops B in
    record
      { Token = TransformerOps.Token ops
      ; Param = TransformerOps.Param ops
      ; forward = forwardOps ops
      ; encode = TransformerKernelBridge.encode B
      ; IsTransformerPolicy = TransformerKernelBridge.IsTransformerPolicy B
      ; encode-is-transformer = TransformerKernelBridge.encode-is-transformer B
      }

  record TransformerTrainingBridge (g : Scale) : Set (lsuc (lsuc ℓ)) where
    field
      bridge : TransformerKernelBridge
      step : RGStep g
      dim : ScalingDimension step
      closed
        : ∀ {c}
          → TransformerKernelBridge.IsTransformerPolicy bridge c
          → TransformerKernelBridge.IsTransformerPolicy bridge (applyRG step c)
      trainParam : TransformerOps.Param (TransformerKernelBridge.ops bridge)
                 → TransformerOps.Param (TransformerKernelBridge.ops bridge)
      train-correct
        : ∀ p
          → TransformerKernelBridge.encode bridge (trainParam p)
            ≡ applyRG step (TransformerKernelBridge.encode bridge p)

  TrainingEndo : Scale → Set (lsuc ℓ)
  TrainingEndo g = RGStep g

  rgStepFromEndo
    : ∀ {g} → TrainingEndo g → RGStep g
  rgStepFromEndo A = A

  record LossData (ops : TransformerOps) : Set (lsuc (lsuc ℓ)) where
    field
      Sample : Set ℓ
      samples : List Sample
      input : Sample → List (TransformerOps.Token ops)
      target : Sample → List (TransformerOps.Token ops)
      loss : List (TransformerOps.Token ops) → List (TransformerOps.Token ops) → Scale
      aggregate : List Scale → Scale

  sumNat : List ℕ → ℕ
  sumNat [] = zero
  sumNat (n ∷ ns) = n + sumNat ns

  record TrainingResources (ops : TransformerOps) : Set (lsuc (lsuc ℓ)) where
    field
      paramCount : TransformerOps.Param ops → ℕ
      tokenCount : List (TransformerOps.Token ops) → ℕ
      flopCount : TransformerOps.Param ops → List (TransformerOps.Token ops) → ℕ
      totalCompute : (D : LossData ops) → TransformerOps.Param ops → ℕ

    sampleTokens : (D : LossData ops) → LossData.Sample D → ℕ
    sampleTokens D s =
      let open LossData D in
      tokenCount (input s) + tokenCount (target s)

    datasetTokens : (D : LossData ops) → ℕ
    datasetTokens D =
      let open LossData D in
      sumNat (map (sampleTokens D) samples)

    sampleFlops : (D : LossData ops) → TransformerOps.Param ops → LossData.Sample D → ℕ
    sampleFlops D p s =
      let open LossData D in
      flopCount p (input s) + flopCount p (target s)

    datasetFlops : (D : LossData ops) → TransformerOps.Param ops → ℕ
    datasetFlops D p =
      let open LossData D in
      sumNat (map (sampleFlops D p) samples)

    totalComputeDefault : (D : LossData ops) → TransformerOps.Param ops → ℕ
    totalComputeDefault D p =
      paramCount p + datasetFlops D p

  record ResourceBudgets (B : TransformerKernelBridge) : Set (lsuc (lsuc ℓ)) where
    private
      ops = TransformerKernelBridge.ops B
    field
      resources : TrainingResources ops
      lossData : LossData ops
      compute : Code → ℕ
      dataBudget : Code → ℕ
      compute-ext : ∀ γ₁ γ₂ → decode γ₁ ≡ decode γ₂ → compute γ₁ ≡ compute γ₂
      data-ext : ∀ γ₁ γ₂ → decode γ₁ ≡ decode γ₂ → dataBudget γ₁ ≡ dataBudget γ₂
      compute-param
        : ∀ p
        → compute (TransformerKernelBridge.paramCode B p)
          ≡ TrainingResources.totalCompute resources lossData p
      data-param
        : ∀ p
        → dataBudget (TransformerKernelBridge.paramCode B p)
          ≡ TrainingResources.datasetTokens resources lossData

  lossParam
    : ∀ {ops} → LossData ops → TransformerOps.Param ops → Scale
  lossParam {ops} D p =
    let open TransformerOps ops in
    let open LossData D in
    aggregate (map (λ s → loss (forwardOps ops p (input s)) (target s)) samples)

  -- Next-token loss model: score predictions against targets.
  record TokenLossModel (ops : TransformerOps) : Set (lsuc (lsuc ℓ)) where
    field
      score : TransformerOps.Token ops → TransformerOps.Token ops → TransformerOps.Scalar ops
      toLoss : TransformerOps.Scalar ops → Scale
      aggregateTokens : List Scale → Scale

  tokenLoss
    : ∀ {ops}
    → TokenLossModel ops
    → List (TransformerOps.Token ops)
    → List (TransformerOps.Token ops)
    → Scale
  tokenLoss {ops} C preds targets =
    let open TokenLossModel C in
    aggregateTokens (zipWith (λ p t → toLoss (score p t)) preds targets)

  record NextTokenLossData (ops : TransformerOps) : Set (lsuc (lsuc ℓ)) where
    field
      Sample : Set ℓ
      samples : List Sample
      prefix : Sample → List (TransformerOps.Token ops)
      nextTokens : Sample → List (TransformerOps.Token ops)
      tokenLossModel : TokenLossModel ops
      aggregateSamples : List Scale → Scale

  nextTokenLossData
    : ∀ {ops} → NextTokenLossData ops → LossData ops
  nextTokenLossData {ops} D =
    record
      { Sample = NextTokenLossData.Sample D
      ; samples = NextTokenLossData.samples D
      ; input = NextTokenLossData.prefix D
      ; target = NextTokenLossData.nextTokens D
      ; loss = tokenLoss (NextTokenLossData.tokenLossModel D)
      ; aggregate = NextTokenLossData.aggregateSamples D
      }

  record LossObservable (ops : TransformerOps) : Set (lsuc (lsuc ℓ)) where
    field
      action : RG.ScaleAction
      obs : Policy → Scale
      mono : ∀ {c d} → _⊑_ c d → QAdapter._≤s_ Q (obs c) (obs d)
      scale : ∀ {g} (s : RGStep g) → ∀ c
            → QAdapter._≤s_ Q
                (obs (applyRG s c))
                (QAdapter._·_ Q (RG.ScaleAction.act action g) (obs c))

  record LossOrderReflecting (obs : Policy → Scale) : Set (lsuc (lsuc ℓ)) where
    field
      reflect : ∀ {c d} → QAdapter._≤s_ Q (obs c) (obs d) → _⊑_ c d

  lossDecrease-stable
    : ∀ {g} {s : RGStep g} (obs : Policy → Scale)
    → LossOrderReflecting obs
    → (∀ c → QAdapter._≤s_ Q (obs (applyRG s c)) (obs c))
    → ∀ c → RGStable s c
  lossDecrease-stable obs O dec c =
    record { closed = LossOrderReflecting.reflect O (dec c) }

  record LossObservableFromData (B : TransformerKernelBridge) : Set (lsuc (lsuc ℓ)) where
    private
      ops = TransformerKernelBridge.ops B
    field
      lossData : LossData ops
      action : RG.ScaleAction
      obs : Policy → Scale
      obs-encode
        : ∀ (p : TransformerOps.Param ops)
        → obs (TransformerKernelBridge.encode B p)
          ≡ lossParam lossData p
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
  record NextTokenLossObservableFromData (B : TransformerKernelBridge) : Set (lsuc (lsuc ℓ)) where
    private
      ops = TransformerKernelBridge.ops B
    field
      lossData : NextTokenLossData ops
      action : RG.ScaleAction
      obs : Policy → Scale
      obs-encode
        : ∀ (p : TransformerOps.Param ops)
        → obs (TransformerKernelBridge.encode B p)
          ≡ lossParam (nextTokenLossData lossData) p
      mono : ∀ {c d} → _⊑_ c d → QAdapter._≤s_ Q (obs c) (obs d)
      scale : ∀ {g} (s : RGStep g) → ∀ c
            → QAdapter._≤s_ Q
                (obs (applyRG s c))
                (QAdapter._·_ Q (RG.ScaleAction.act action g) (obs c))

    asLossObservableFromData : LossObservableFromData B
    asLossObservableFromData =
      record
        { lossData = nextTokenLossData lossData
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
      bridge : TransformerKernelBridge
      endo : TrainingEndo g
      lossObsData : LossObservableFromData bridge
      closed
        : ∀ {c}
          → TransformerKernelBridge.IsTransformerPolicy bridge c
          → TransformerKernelBridge.IsTransformerPolicy bridge
              (applyRG (rgStepFromEndo endo) c)
      trainParam : TransformerOps.Param (TransformerKernelBridge.ops bridge)
                 → TransformerOps.Param (TransformerKernelBridge.ops bridge)
      train-correct
        : ∀ p
          → TransformerKernelBridge.encode bridge (trainParam p)
            ≡ applyRG (rgStepFromEndo endo) (TransformerKernelBridge.encode bridge p)

    lossObs : LossObservable (TransformerKernelBridge.ops bridge)
    lossObs = LossObservableFromData.asLossObservable lossObsData

  record OptimizerTraining (g : Scale) : Set (lsuc (lsuc ℓ)) where
    field
      spec : TrainingSpec g
      lossOrder : LossOrderReflecting
        (LossObservableFromData.obs (TrainingSpec.lossObsData spec))
      lossDecrease
        : ∀ p
        → QAdapter._≤s_ Q
            (lossParam (LossObservableFromData.lossData (TrainingSpec.lossObsData spec))
              (TrainingSpec.trainParam spec p))
            (lossParam (LossObservableFromData.lossData (TrainingSpec.lossObsData spec)) p)

  optimizer-policy-decrease
    : ∀ {g} (O : OptimizerTraining g)
    → ∀ p
    → QAdapter._≤s_ Q
        (LossObservableFromData.obs (TrainingSpec.lossObsData (OptimizerTraining.spec O))
          (applyRG (rgStepFromEndo (TrainingSpec.endo (OptimizerTraining.spec O)))
            (TransformerKernelBridge.encode (TrainingSpec.bridge (OptimizerTraining.spec O)) p)))
        (LossObservableFromData.obs (TrainingSpec.lossObsData (OptimizerTraining.spec O))
          (TransformerKernelBridge.encode (TrainingSpec.bridge (OptimizerTraining.spec O)) p))
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
        step1 : QAdapter._≤s_ Q (obs (TransformerKernelBridge.encode B (upd p)))
                               (lossParam lossD p)
        step1 =
          subst
            (λ x → QAdapter._≤s_ Q x (lossParam lossD p))
            (sym obsUpd)
            (lossDecrease p)
        step2 : QAdapter._≤s_ Q (obs (TransformerKernelBridge.encode B (upd p)))
                               (obs (TransformerKernelBridge.encode B p))
        step2 =
          subst
            (λ x → QAdapter._≤s_ Q (obs (TransformerKernelBridge.encode B (upd p))) x)
            (sym obsP)
            step1
    in
    subst
      (λ x → QAdapter._≤s_ Q (obs x) (obs (TransformerKernelBridge.encode B p)))
      (TrainingSpec.train-correct S p)
      step2

  optimizer-param-stable
    : ∀ {g} (O : OptimizerTraining g)
    → ∀ p
    → RGStable
        (rgStepFromEndo (TrainingSpec.endo (OptimizerTraining.spec O)))
        (TransformerKernelBridge.encode (TrainingSpec.bridge (OptimizerTraining.spec O)) p)
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
        (TransformerKernelBridge.encode
          (TrainingSpec.bridge (OptimizerTraining.spec (SGDTraining.optimizer S))) p)
  sgd-param-stable S = optimizer-param-stable (SGDTraining.optimizer S)

  adam-param-stable
    : ∀ {g} (A : AdamTraining g)
    → ∀ p
    → RGStable
        (rgStepFromEndo (TrainingSpec.endo (OptimizerTraining.spec (AdamTraining.optimizer A))))
        (TransformerKernelBridge.encode
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
    → TF.TrainingDynamics (coreFromBridge (TrainingSpec.bridge S)) g
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
    → TF.TrainingDynamics (coreFromBridge (TransformerTrainingBridge.bridge B)) g
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
    → (p : TransformerOps.Param (TransformerKernelBridge.ops (TransformerTrainingBridge.bridge B)))
    → TF.IsTransformerCode
        (coreFromBridge (TransformerTrainingBridge.bridge B))
        (TransformerKernelBridge.paramCode (TransformerTrainingBridge.bridge B) p)
  paramIsTransformer B p =
    let open TransformerKernelBridge (TransformerTrainingBridge.bridge B) in
    subst IsTransformerPolicy (sym (paramCode-decode p)) (encode-is-transformer p)

  trainParam-code
    : ∀ {g} (B : TransformerTrainingBridge g)
    → (p : TransformerOps.Param (TransformerKernelBridge.ops (TransformerTrainingBridge.bridge B)))
    → decode (TransformerKernelBridge.paramCode (TransformerTrainingBridge.bridge B)
              (TransformerTrainingBridge.trainParam B p))
      ≡
      applyRG (TransformerTrainingBridge.step B)
        (decode (TransformerKernelBridge.paramCode (TransformerTrainingBridge.bridge B) p))
  trainParam-code B p =
    let open TransformerKernelBridge (TransformerTrainingBridge.bridge B) in
    let s = TransformerTrainingBridge.step B in
    trans
      (trans
        (paramCode-decode (TransformerTrainingBridge.trainParam B p))
        (TransformerTrainingBridge.train-correct B p))
      (cong (applyRG s) (sym (paramCode-decode p)))

  paramStable-scalingBound
    : ∀ {g} (B : TransformerTrainingBridge g)
    → (p : TransformerOps.Param (TransformerKernelBridge.ops (TransformerTrainingBridge.bridge B)))
    → RGStable (TransformerTrainingBridge.step B)
        (TransformerKernelBridge.encode (TransformerTrainingBridge.bridge B) p)
    → SL.ScalingBound (TransformerTrainingBridge.step B) (TransformerTrainingBridge.dim B)
        (TransformerKernelBridge.paramCode (TransformerTrainingBridge.bridge B) p)
  paramStable-scalingBound B p st =
    let open TransformerKernelBridge (TransformerTrainingBridge.bridge B) in
    let st' = TF.stable-subst (sym (paramCode-decode p)) st in
    SL.scalingBound-from-stable
      (TransformerTrainingBridge.step B)
      (TransformerTrainingBridge.dim B)
      st'
