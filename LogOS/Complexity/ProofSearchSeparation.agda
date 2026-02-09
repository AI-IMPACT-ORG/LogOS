{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.ProofSearchSeparation where

-- Narrative-first entrypoint:
-- “verification vs search” (proof checking vs proof existence / proof search),
-- stated in a resource-aware way so physical axiom packs can plug in.

import LogOS.Complexity.ResourceSchemaG as ResourceSchemaGₜ
import LogOS.Complexity.ResourceSchemaGraded as ResourceSchemaGradedₜ
import LogOS.Complexity.ObservabilityBudgetG as ObservabilityBudgetGₜ
import LogOS.Complexity.ObservabilityBudgetGraded as ObservabilityBudgetGradedₜ
import LogOS.Complexity.ProofSearchBoundary as ProofSearchBoundaryₜ
import LogOS.Complexity.ProofSearchCapstoneGraded as ProofSearchCapstoneGradedₜ
import LogOS.Complexity.Targets.ProofSearchChainedTheoremGraded as ProofSearchChainedTheoremGradedₜ
import LogOS.Complexity.Targets.ProofSearchQuantumPivotGraded as ProofSearchQuantumPivotGradedₜ
import LogOS.Complexity.Targets.ProofSearchGraded as ProofSearchGradedₜ
import LogOS.Complexity.Targets.StablePProofSearchReflectionBarrier as StablePProofSearchReflectionBarrierₜ
import LogOS.Complexity.PhysToTruthRouteBridge as PhysToTruthRouteBridgeₜ
import LogOS.Complexity.ProofSearchOpacitySpine as ProofSearchOpacitySpineₜ

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
