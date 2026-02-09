{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.All where

-- Minimal library test aggregator:
-- typecheck the public API and the core theorem surfaces.

open import LogOS.API.Kernel
open import LogOS.Kernel
open import LogOS.Kernel.TierCategorical
open import LogOS.Kernel.Endo

open import LogOS.Theorems.Core
open import LogOS.Theorems.Infinite
open import LogOS.Theorems.OS

-- Additional aggregation surfaces: keep “All” entrypoints typecheckable.
import LogOS.Theorems.CategoryTheory.All as CatTheory
import LogOS.Theorems.Modal.All as ModalTheorems
import LogOS.Theorems.Reflection.All as ReflectionTheorems
import LogOS.Kernel.Graded.All as GradedKernelAll
import LogOS.Theorems.Boundary.Graded.All as GradedBoundaryTheorems
import LogOS.Minimal.Constraints as Constraints
import LogOS.Minimal.ConstraintsIndexed as ConstraintsIndexed
import LogOS.Minimal.ConstraintsOverSig as ConstraintsOverSig
import LogOS.Theorems.Meta.Bootstrapping as Bootstrapping

-- Publication-facing packs should stay typecheckable from a single entrypoint.
import LogOS.Packs.ZFC.All as PacksZFC

-- Proof-theoretic layer (FOL + ZFC façade).
import LogOS.ObjectLogic.ZFC.All as LogicZFC

-- While small-step meta-theory (progress/preservation/determinism).
import LogOS.UniversalIR.While.SmallStep as WhileSmallStep

-- Kernel extension sanity checks
import Tests.Kernel.Graded
import Tests.ObservedKernel
import Tests.BoxModality
import Tests.BudgetedCommunicableTruth
import Tests.CategoryTheoryCoherence
import Tests.AssumptionsBundles
import Tests.AssumptionsSeparation
import Tests.PacksThreading
import Tests.PortSpineOnly
import Tests.InterlinguaMu
import Tests.InterlinguaMuNontrivial
import Tests.MuInterlinguaWrappers
import Tests.ProcessLimitMuFusion
import Tests.OmegaCPOMap2Cat
import Tests.Presentation2Cat
import Tests.Process2Cat
import Tests.Kernel2CatGuards
import Tests.APISurface

-- Coherence regression: curated public surfaces stay stable.
import Tests.CoherenceSurfaces
import Tests.SmokeSurfaces

-- Stable pack surfaces: keep each stable `LogOS.Packs.*.Surface` in CI, with a
-- shared non-triviality witness for the ports/adapters spine.
import Tests.PacksAgentsNontrivial
import Tests.PacksAssumptionsNontrivial
import Tests.PacksInfoTheoryNontrivial
import Tests.PacksUniversalIRNontrivial
import Tests.PacksUniversalityNontrivial
import Tests.PacksZFCNontrivial

-- View coherence: the “one system, many views” bridge points typecheck together.
import Tests.ViewsMetaTheory
