{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Resources where

open import LogOS.Prelude

open import LogOS.Prelude.List using (List; []; _∷_; map)
open import LogOS.Prelude using (ℕ; zero; _+_)

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)
open import LogOS.Kernel.Eq using (module ForGradedKernel)

import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Ops as Ops
import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.KernelBridge as KB
import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Loss as Loss

-- Resource bookkeeping: parameters/tokens/flops + extensional budgets on codes.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module OpsFor = Ops.For K ωCPO
  module KBFor = KB.For K ωCPO
  module LossFor = Loss.For K ωCPO

  open GradedKernel K using (Code)
  open ForGradedKernel K using (_≃K_)

  sumNat : List ℕ → ℕ
  sumNat [] = zero
  sumNat (n ∷ ns) = n + sumNat ns

  record TrainingResources (ops : OpsFor.TransformerOps) : Set (lsuc (lsuc ℓ)) where
    field
      paramCount : OpsFor.TransformerOps.Param ops → ℕ
      tokenCount : List (OpsFor.TransformerOps.Token ops) → ℕ
      flopCount : OpsFor.TransformerOps.Param ops → List (OpsFor.TransformerOps.Token ops) → ℕ
      totalCompute : (D : LossFor.LossData ops) → OpsFor.TransformerOps.Param ops → ℕ

    sampleTokens : (D : LossFor.LossData ops) → LossFor.LossData.Sample D → ℕ
    sampleTokens D s =
      let open LossFor.LossData D in
      tokenCount (input s) + tokenCount (target s)

    datasetTokens : (D : LossFor.LossData ops) → ℕ
    datasetTokens D =
      let open LossFor.LossData D in
      sumNat (map (sampleTokens D) samples)

    sampleFlops : (D : LossFor.LossData ops) → OpsFor.TransformerOps.Param ops → LossFor.LossData.Sample D → ℕ
    sampleFlops D p s =
      let open LossFor.LossData D in
      flopCount p (input s) + flopCount p (target s)

    datasetFlops : (D : LossFor.LossData ops) → OpsFor.TransformerOps.Param ops → ℕ
    datasetFlops D p =
      let open LossFor.LossData D in
      sumNat (map (sampleFlops D p) samples)

    totalComputeDefault : (D : LossFor.LossData ops) → OpsFor.TransformerOps.Param ops → ℕ
    totalComputeDefault D p =
      paramCount p + datasetFlops D p

  record ResourceBudgets (B : KBFor.TransformerKernelBridge) : Set (lsuc (lsuc ℓ)) where
    private
      ops = KBFor.TransformerKernelBridge.ops B
    field
      resources : TrainingResources ops
      lossData : LossFor.LossData ops
      compute : Code → ℕ
      dataBudget : Code → ℕ
      compute-ext : ∀ γ₁ γ₂ → γ₁ ≃K γ₂ → compute γ₁ ≡ compute γ₂
      data-ext : ∀ γ₁ γ₂ → γ₁ ≃K γ₂ → dataBudget γ₁ ≡ dataBudget γ₂
      compute-param
        : ∀ p
        → compute (KBFor.TransformerKernelBridge.paramCode B p)
          ≡ TrainingResources.totalCompute resources lossData p
      data-param
        : ∀ p
        → dataBudget (KBFor.TransformerKernelBridge.paramCode B p)
          ≡ TrainingResources.datasetTokens resources lossData

