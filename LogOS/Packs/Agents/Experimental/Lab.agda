{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Lab where

-- Experimental extensions to the Agents lab surface.
-- Includes transformer/scaling arguments plus complexity-dependent physics/RG-flow.
-- Combine with `LogOS.Packs.Agents.Lab.All` for the full lab story.

module Arguments where
  module ScalingLaws where
    open import LogOS.Packs.Agents.Experimental.Arguments.ScalingLaws public
  module LearningScaling where
    open import LogOS.Packs.Agents.Experimental.Arguments.LearningScaling public
  module TransformerScaling where
    open import LogOS.Packs.Agents.Experimental.Arguments.TransformerScaling public
  module TransformerFormalization where
    open import LogOS.Packs.Agents.Experimental.Arguments.TransformerFormalization public
  module TransformerBridge where
    open import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge public
  module TransformerScalingPipeline where
    open import LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline public
  module Transformer where
    open import LogOS.Packs.Agents.Experimental.Arguments.Transformer public
  module LogOSDiscoveryScaling where
    open import LogOS.Packs.Agents.Experimental.Arguments.LogOSDiscoveryScaling public
  module KolmogorovDiscoveryScaling where
    open import LogOS.Packs.Agents.Experimental.Arguments.KolmogorovDiscoveryScaling public
  module KolmogorovOptimality where
    open import LogOS.Packs.Agents.Experimental.Arguments.KolmogorovOptimality public
  module SolomonoffLearning where
    open import LogOS.Packs.Agents.Experimental.Arguments.SolomonoffLearning public
  module TransformerKolmogorovScaling where
    open import LogOS.Packs.Agents.Experimental.Arguments.TransformerKolmogorovScaling public

module Emit where
  module TransformerTF where
    open import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Emit public

module Learning where
  module RGFlow where
    open import LogOS.Packs.Agents.Experimental.Learning.RGFlow public

module Physics where
  open import LogOS.Packs.Agents.Experimental.Physics.All public

module Safety where
  module NoTotalAuditor where
    open import LogOS.Packs.Agents.Experimental.Safety.NoTotalAuditor public

module Capstone where
  open import LogOS.Packs.Agents.Experimental.Capstone public

module Core where
  open import LogOS.Packs.Agents.Lab.Core public

  open import LogOS.Prelude
  open import LogOS.Base.Signature using (LogOSSignature)
  open import LogOS.Minimal.Adapter using (QAdapter)
  open import LogOS.Minimal.Con using (BulkBoundary)
  open import LogOS.Minimal.Truth as Truth
  import LogOS.Kernel.Graded as GK
  open import LogOS.Packs.Agents.Socket.Core using (AgentSocket)
  import LogOS.Packs.Agents.Experimental.Physics.MaxwellAgent as MaxwellAgent
  import LogOS.Packs.Agents.Experimental.Physics.LearningCost as LearningCostPkg
  import LogOS.Packs.Agents.Experimental.Learning.RGFlow as RGFlow

  -- Experimental extension: restore the physics/RG-flow hooks dropped from the
  -- stable core surface.
  module ForExperimental
    {ℓ ℓTask : Level}
    {Sig  : LogOSSignature ℓ}
    {Q    : QAdapter ℓ}
    {Task : Set ℓTask}
    (Sock : AgentSocket Sig Q Task)
    where

    open LogOS.Packs.Agents.Lab.Core.For Sock public

    module LearningCost = LearningCostPkg.For Sock
    module Maxwell      = MaxwellAgent.For Sock

    module GradedPhysics (K : GK.GradedKernel Sig Q) where
      module LC = LearningCostPkg.For Sock
      module SoftPhysics = LC.Graded K
      module RG (ωCPO : (let module GT = Truth.GuardedCore in GT.OmegaCPO)
                        (BulkBoundary.bnd (GK.GradedKernel.BB K))) where
        module Flow = RGFlow.For K ωCPO
