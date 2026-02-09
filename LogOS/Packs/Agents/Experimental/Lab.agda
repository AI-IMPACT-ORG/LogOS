{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Lab where

-- Experimental extensions to the Agents lab surface.
-- Includes transformer/scaling arguments plus complexity-dependent physics/RG-flow.
-- Combine with `LogOS.Packs.Agents.Lab.All` for the full lab story.

module Arguments where
  -- Anchor modules for reachability/discoverability (kept namespaced).
  import LogOS.Packs.Agents.Experimental.Arguments.ScalingLaws as ScalingLaws
  import LogOS.Packs.Agents.Experimental.Arguments.LearningScaling as LearningScaling
  import LogOS.Packs.Agents.Experimental.Arguments.TransformerScaling as TransformerScaling
  import LogOS.Packs.Agents.Experimental.Arguments.ControlledFeedback as ControlledFeedback
  import LogOS.Packs.Agents.Experimental.Arguments.TransformerFormalization as TransformerFormalization
  import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge as TransformerBridge
  import LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline as TransformerScalingPipeline
  import LogOS.Packs.Agents.Experimental.Arguments.Transformer as Transformer
  import LogOS.Packs.Agents.Experimental.Arguments.Scaling as Scaling
  import LogOS.Packs.Agents.Experimental.Arguments.Discovery as Discovery
  import LogOS.Packs.Agents.Experimental.Arguments.DiscoveryScaling as DiscoveryScaling
  import LogOS.Packs.Agents.Experimental.Arguments.KolmogorovDiscoveryScaling as KolmogorovDiscoveryScaling
  import LogOS.Packs.Agents.Experimental.Arguments.KolmogorovOptimality as KolmogorovOptimality
  import LogOS.Packs.Agents.Experimental.Arguments.SolomonoffLearning as SolomonoffLearning
  import LogOS.Packs.Agents.Experimental.Arguments.TransformerKolmogorovScaling as TransformerKolmogorovScaling

  -- Kept lightweight: import the individual modules directly as needed.
  --
  -- Transformer/scaling:
  -- - `LogOS.Packs.Agents.Experimental.Arguments.ScalingLaws`
  -- - `LogOS.Packs.Agents.Experimental.Arguments.LearningScaling`
  -- - `LogOS.Packs.Agents.Experimental.Arguments.TransformerScaling`
  -- - `LogOS.Packs.Agents.Experimental.Arguments.ControlledFeedback`
  -- - `LogOS.Packs.Agents.Experimental.Arguments.TransformerFormalization`
  -- - `LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge`
  -- - `LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline`
  -- - `LogOS.Packs.Agents.Experimental.Arguments.Transformer`
  -- - `LogOS.Packs.Agents.Experimental.Arguments.TransformerKolmogorovScaling`
  --
  -- Discovery scaling (optional):
  -- - `LogOS.Packs.Agents.Experimental.Arguments.DiscoveryScaling`
  -- - `LogOS.Packs.Agents.Experimental.Arguments.KolmogorovDiscoveryScaling`
  -- - `LogOS.Packs.Agents.Experimental.Arguments.KolmogorovOptimality`
  -- - `LogOS.Packs.Agents.Experimental.Arguments.SolomonoffLearning`

module Emit where
  -- Anchor modules for reachability/discoverability (kept namespaced).
  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.DataPlan as TensorFlowDataPlan
  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Emit as TensorFlowEmit
  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.EmitBridge as TensorFlowEmitBridge
  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.EmitCore as TensorFlowEmitCore
  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Features.Coupling as TensorFlowCoupling
  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Features.Symbolic as TensorFlowSymbolic
  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Features.Telemetry as TensorFlowTelemetry
  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Pipeline as TensorFlowPipeline
  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Syntax as TensorFlowSyntax
  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.SyntaxCore as TensorFlowSyntaxCore
  import LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Types as TensorFlowTypes

  -- Kept lightweight: import the backend directly.
  -- - `LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Emit`
  -- - `LogOS.Packs.Agents.Experimental.Emit.Backends.TensorFlow.Syntax`

module Learning where
  import LogOS.Packs.Agents.Experimental.Learning.RGFlow as RGFlow
  -- Kept lightweight: import directly.
  -- - `LogOS.Packs.Agents.Experimental.Learning.RGFlow`

module Physics where
  import LogOS.Packs.Agents.Experimental.Physics.All as All
  -- Kept lightweight: import directly.
  -- - `LogOS.Packs.Agents.Experimental.Physics.All`

module Safety where
  import LogOS.Packs.Agents.Experimental.Safety.NoTotalAuditor as NoTotalAuditor
  -- Kept lightweight: import directly.
  -- - `LogOS.Packs.Agents.Experimental.Safety.NoTotalAuditor`

module Frameworks where
  -- Meta-reasoning / diagonal-barrier surfaces are intentionally kept here
  -- (experimental): they depend on explicit diagonalisation assumption packs.
  open import LogOS.Packs.Agents.Frameworks.GodelMachine public
  open import LogOS.Packs.Agents.Frameworks.MetaReasoning public

module Comparisons where
  -- Limitation theorems are diagonal/barrier results, hence experimental.
  open import LogOS.Packs.Agents.Comparisons.Limitations public

module Examples where
  -- Domain-facing examples are kept out of the stable surface to preserve the
  -- “stable roots do not reach `LogOS.Domain.*` transitively” policy.
  open import LogOS.Packs.Agents.Examples.ReindexedNetwork public

module Capstone where
  import LogOS.Packs.Agents.Experimental.Capstone as Capstone
  -- Kept lightweight: import directly.
  -- - `LogOS.Packs.Agents.Experimental.Capstone`

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
