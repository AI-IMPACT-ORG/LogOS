{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.Targets.All where

-- Index module for the Complexity targets namespace (discoverability only).

import LogOS.Complexity.Targets.SAT as SATₜ
import LogOS.Complexity.Targets.SATProofSearch as SATProofSearchₜ
import LogOS.Complexity.Targets.ProofSearchGraded as ProofSearchGradedₜ
import LogOS.Complexity.Targets.ProofSearchChainedTheoremGraded as ProofSearchChainedTheoremGradedₜ
import LogOS.Complexity.Targets.ProofSearchQuantumPivotGraded as ProofSearchQuantumPivotGradedₜ
import LogOS.Complexity.Targets.StablePProofSearchReflectionBarrier as StablePProofSearchReflectionBarrierₜ

module SAT = SATₜ
module SATProofSearch = SATProofSearchₜ
module ProofSearchGraded = ProofSearchGradedₜ
module ProofSearchChainedTheoremGraded = ProofSearchChainedTheoremGradedₜ
module ProofSearchQuantumPivotGraded = ProofSearchQuantumPivotGradedₜ
module StablePProofSearchReflectionBarrier = StablePProofSearchReflectionBarrierₜ

