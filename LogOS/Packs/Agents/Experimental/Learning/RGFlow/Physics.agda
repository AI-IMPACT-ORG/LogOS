{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Learning.RGFlow.Physics where

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Kernel.Graded using (GradedKernel)
open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
import LogOS.Packs.Agents.Experimental.Physics.LearningCost as LearningCost
import LogOS.Theorems.Meta.LandauerIO as LIO

import LogOS.Packs.Agents.Experimental.Learning.RGFlow.Core as Core

-- Optional physics overlay for RG-flow learning: Landauer bounds.

module For
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
            (BulkBoundary.bnd (GradedKernel.BB K)))
  where

  module CoreFor = Core.For K ωCPO
  open CoreFor using (RGStep)

  module Physics
    {ℓTask : Level}
    {Task : Set ℓTask}
    (Sock : AgentSocket Sig Q Task)
    where

    module LC = LearningCost.For Sock
    module SoftPhys = LC.Graded K

    rg-learning-cost
      : (A : SoftPhys.SoftLearningAssumptions)
      → ∀ {g} (s : RGStep g)
      → QAdapter._≤s_ Q
          (LIO.LandauerIOAssumptions.L (SoftPhys.SoftLearningAssumptions.landauer A))
          (LIO.LandauerIOAssumptions.cost (SoftPhys.SoftLearningAssumptions.landauer A)
            (SoftPhys.SoftLearningAssumptions.stepProgram A s))
    rg-learning-cost A s = SoftPhys.soft-learning-cost A s

