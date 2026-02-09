{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.KernelBridge where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Ops as Ops
import LogOS.Packs.Agents.Experimental.Arguments.TransformerFormalization as TransformerFormalization
import LogOS.Packs.Agents.Experimental.Arguments.ControlledFeedback as ControlledFeedback

-- Bridge from a concrete transformer parameter space to kernel-native policies/codes.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module OpsFor = Ops.For K ωCPO
  open OpsFor using (TransformerOps; forwardOps)

  module TF = TransformerFormalization.For K ωCPO
  module CF = ControlledFeedback.For K ωCPO

  open GradedKernel K using (BB; Code; decode; encode; decode∘encode)
  open BulkBoundary BB using (Con_bnd)

  record TransformerKernelBridge : Set (lsuc (lsuc ℓ)) where
    field
      ops : TransformerOps
      encode : TransformerOps.Param ops → Con_bnd
      IsTransformerPolicy : Con_bnd → Set ℓ
      encode-is-transformer : ∀ p → IsTransformerPolicy (encode p)
      paramCode : TransformerOps.Param ops → Code
      paramCode-decode : ∀ p → decode (paramCode p) ≡ encode p

  module CanonicalEncoding
    (ops : TransformerOps)
    (encodeParam : TransformerOps.Param ops → Con_bnd)
    (IsTransformerPolicy : Con_bnd → Set ℓ)
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

  controlledFromBridge : TransformerKernelBridge → CF.ControlledFeedbackCore
  controlledFromBridge B =
    let ops = TransformerKernelBridge.ops B in
    record
      { Param = TransformerOps.Param ops
      ; encode = TransformerKernelBridge.encode B
      ; IsControlledPolicy = TransformerKernelBridge.IsTransformerPolicy B
      ; encode-is-controlled = TransformerKernelBridge.encode-is-transformer B
      }
