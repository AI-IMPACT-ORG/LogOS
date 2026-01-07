{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.SmokeSurfaces where

-- Smoke-test a small set of public-facing entrypoints that are otherwise only
-- referenced from prose docs. This keeps those modules typechecked in CI.

open import LogOS.Algebra.Braiding
open import LogOS.Algebra.GraphSurface
open import LogOS.Algebra.PolyOps

open import LogOS.Domain.Complexity.Targets.SATProofSearch
open import LogOS.Domain.Opacity.NumberTheory.LFunction.Selberg
open import LogOS.Domain.Opacity.SpectralFromFacts
open import LogOS.Domain.ZFC.SetTheory.Derived
open import LogOS.Domain.UniversalIR.Walkthrough
open import LogOS.Domain.ZFC.Supplementary.HF.HFGraph
open import Tests.ContinuityOne

open import LogOS.Packs.InfoTheory.Core

open import LogOS.Theorems.BoundaryFixFromScott
open import LogOS.Theorems.CategoryTheory.All
open import LogOS.Theorems.Meta.All
open import LogOS.Theorems.Meta.FlowCurvature
open import LogOS.Theorems.Meta.Godel
open import LogOS.Theorems.Meta.MathPhysSynthesis
open import LogOS.Theorems.Meta.Rice
