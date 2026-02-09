{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.SmokeSurfaces where

-- Smoke-test a small set of public-facing entrypoints that are otherwise only
-- referenced from prose docs. This keeps those modules typechecked in CI.

-- Core/All/Surface conventions (navigation + stable entrypoints).
import LogOS.Kernel.Surface
import LogOS.Kernel.All
import LogOS.Ports.Core
import LogOS.Ports.Surface
import LogOS.Ports.All
import LogOS.Adapters.Core
import LogOS.Adapters.Surface
import LogOS.Adapters.All
import LogOS.Theorems.Surface
import LogOS.Theorems.All
import LogOS.Domain.Surface

open import LogOS.Theorems.Boundary.Kernel.Braiding
open import LogOS.Algebra.GraphSurface
open import LogOS.Algebra.PolyOps

open import LogOS.Complexity.Targets.SATProofSearch
open import LogOS.Domain.Opacity.NumberTheory.LFunction.Selberg
open import LogOS.Domain.Opacity.SpectralFromFacts
open import LogOS.ZFC.SetTheory.Derived
open import LogOS.UniversalIR.Walkthrough
open import LogOS.ZFC.Supplementary.HF.HFGraph
open import Tests.ContinuityOne

open import LogOS.Packs.InfoTheory.Core

open import LogOS.Theorems.BoundaryFixFromScott
open import LogOS.Theorems.CategoryTheory.All
open import LogOS.Theorems.Meta.All
open import LogOS.Theorems.Meta.FlowCurvature
open import LogOS.Theorems.Meta.Godel
open import LogOS.Theorems.Meta.MathPhysSynthesis
open import LogOS.Theorems.Meta.Rice
