{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.All where

-- Minimal library test aggregator:
-- typecheck the public API and the core theorem surfaces.

open import LogOS.API.Minimal
open import LogOS.API.LogicKernel
open import LogOS.Kernel
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
import LogOS.Free.All as FreeAll

-- Publication-facing packs should stay typecheckable from a single entrypoint.
import LogOS.Packs.ZFC.All as PacksZFC

-- Proof-theoretic layer (FOL + ZFC façade).
import LogOS.ObjectLogic.ZFC.All as LogicZFC

-- Kernel extension sanity checks
import Tests.Kernel.Graded

-- Coherence regression: curated public surfaces stay stable.
import Tests.CoherenceSurfaces
import Tests.SmokeSurfaces

-- View coherence: the “one system, many views” bridge points typecheck together.
import Tests.ViewsMetaTheory
