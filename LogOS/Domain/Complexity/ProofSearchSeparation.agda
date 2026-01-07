{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.ProofSearchSeparation where

-- Narrative-first entrypoint:
-- “verification vs search” (proof checking vs proof existence / proof search),
-- stated in a resource-aware way so physical axiom packs can plug in.

import LogOS.Domain.Complexity.ResourceSchemaG as ResourceSchemaGₜ
import LogOS.Domain.Complexity.ResourceSchemaGraded as ResourceSchemaGradedₜ
import LogOS.Domain.Complexity.ObservabilityBudgetG as ObservabilityBudgetGₜ
import LogOS.Domain.Complexity.ObservabilityBudgetGraded as ObservabilityBudgetGradedₜ
import LogOS.Domain.Complexity.ProofSearchBoundary as ProofSearchBoundaryₜ
import LogOS.Domain.Complexity.ProofSearchCapstoneGraded as ProofSearchCapstoneGradedₜ
import LogOS.Domain.Complexity.Targets.ProofSearchChainedTheoremGraded as ProofSearchChainedTheoremGradedₜ
import LogOS.Domain.Complexity.Targets.ProofSearchQuantumPivotGraded as ProofSearchQuantumPivotGradedₜ
import LogOS.Domain.Complexity.Targets.ProofSearchGraded as ProofSearchGradedₜ
import LogOS.Domain.Complexity.Targets.StablePProofSearchReflectionBarrier as StablePProofSearchReflectionBarrierₜ
import LogOS.Domain.Complexity.PhysToTruthRouteBridge as PhysToTruthRouteBridgeₜ
import LogOS.Domain.Complexity.ProofSearchOpacitySpine as ProofSearchOpacitySpineₜ

module ResourceSchemaG = ResourceSchemaGₜ
module ResourceSchemaGraded = ResourceSchemaGradedₜ
module ObservabilityBudgetG = ObservabilityBudgetGₜ
module ObservabilityBudgetGraded = ObservabilityBudgetGradedₜ
module ProofSearchBoundary = ProofSearchBoundaryₜ
module ProofSearchCapstoneGraded = ProofSearchCapstoneGradedₜ
module ProofSearchChainedTheoremGraded = ProofSearchChainedTheoremGradedₜ
module ProofSearchQuantumPivotGraded = ProofSearchQuantumPivotGradedₜ
module ProofSearchGraded = ProofSearchGradedₜ
module StablePProofSearchReflectionBarrier = StablePProofSearchReflectionBarrierₜ
module PhysToTruthRouteBridge = PhysToTruthRouteBridgeₜ
module ProofSearchOpacitySpine = ProofSearchOpacitySpineₜ
