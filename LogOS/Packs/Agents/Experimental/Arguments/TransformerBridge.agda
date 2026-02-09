{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)

import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Ops as OpsMod
import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.KernelBridge as KernelBridgeMod
import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Loss as LossMod
import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Resources as ResourcesMod
import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Training as TrainingMod
import LogOS.Packs.Agents.Experimental.Arguments.Context as Ctx

-- Bridge from concrete transformer structure to kernel-native training/scaling.
-- Split into concern-based submodules; this file is a stable wrapper surface.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module Ops = OpsMod.For K ωCPO

  module KernelBridge = KernelBridgeMod.For K ωCPO
  open KernelBridge public
    using (TransformerKernelBridge; coreFromBridge; controlledFromBridge)

  module Loss = LossMod.For K ωCPO
  open Loss public
    using (LossData; lossParam; TokenLossModel; tokenLoss; NextTokenLossData; nextTokenLossData)

  module Resources = ResourcesMod.For K ωCPO
  open Resources public using (sumNat; TrainingResources; ResourceBudgets)

  module Training = TrainingMod.For K ωCPO

module Ops where
  open import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Ops public

module KernelBridge where
  open import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.KernelBridge public

module Loss where
  open import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Loss public

module Resources where
  open import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Resources public

module Training where
  open import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge.Training public

-- Context-bundled entrypoint (convenience).
