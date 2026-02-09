{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Loss where

open import LogOS.Prelude

open import LogOS.Prelude.List using (List; map; zipWith)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Ops as Ops

-- Loss/data layer for the transformer bridge (still abstract over concrete loss).

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module OpsFor = Ops.For K ωCPO

  open QAdapter Q using (Scale)

  record LossData (ops : OpsFor.TransformerOps) : Set (lsuc (lsuc ℓ)) where
    field
      Sample : Set ℓ
      samples : List Sample
      input : Sample → List (OpsFor.TransformerOps.Token ops)
      target : Sample → List (OpsFor.TransformerOps.Token ops)
      loss : List (OpsFor.TransformerOps.Token ops)
          → List (OpsFor.TransformerOps.Token ops)
          → Scale
      aggregate : List Scale → Scale

  lossParam
    : ∀ {ops} → LossData ops → OpsFor.TransformerOps.Param ops → Scale
  lossParam {ops} D p =
    let open OpsFor.TransformerOps ops in
    let open LossData D in
    aggregate (map (λ s → loss (OpsFor.forwardOps ops p (input s)) (target s)) samples)

  -- Next-token loss model: score predictions against targets.
  record TokenLossModel (ops : OpsFor.TransformerOps) : Set (lsuc (lsuc ℓ)) where
    field
      score : OpsFor.TransformerOps.Token ops → OpsFor.TransformerOps.Token ops
            → OpsFor.TransformerOps.Scalar ops
      toLoss : OpsFor.TransformerOps.Scalar ops → Scale
      aggregateTokens : List Scale → Scale

  tokenLoss
    : ∀ {ops}
    → TokenLossModel ops
    → List (OpsFor.TransformerOps.Token ops)
    → List (OpsFor.TransformerOps.Token ops)
    → Scale
  tokenLoss {ops} C preds targets =
    let open TokenLossModel C in
    aggregateTokens (zipWith (λ p t → toLoss (score p t)) preds targets)

  record NextTokenLossData (ops : OpsFor.TransformerOps) : Set (lsuc (lsuc ℓ)) where
    field
      Sample : Set ℓ
      samples : List Sample
      prefix : Sample → List (OpsFor.TransformerOps.Token ops)
      nextTokens : Sample → List (OpsFor.TransformerOps.Token ops)
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

