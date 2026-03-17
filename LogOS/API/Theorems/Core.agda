{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Theorems.Core where

-- Small, load-bearing theorems (tooling loops) that are reused across packs.

open import LogOS.LT.Presentation.ObservationInitiality public
open import LogOS.LT.Presentation.Independence public
open import LogOS.LT.Presentation.ExtensionalMinimality public
open import LogOS.LT.Theorems.ArchitecturalNormalForm public
open import LogOS.LT.Theorems.EvaluatorReflection public
open import LogOS.LT.Presentation.Transport public
open import LogOS.LT.Presentation.Interlingua public
open import LogOS.LT.Theorems.Effectivisation public
open import LogOS.LT.Theorems.StableCompletion public
open import LogOS.LT.Theorems.ProbeSuiteRepresentation public
open import LogOS.LT.Theorems.DependentProbeSuiteRepresentation public
open import LogOS.LT.Theorems.EffectivePackets public
open import LogOS.LT.Theorems.PacketCorollaries public
open import LogOS.LT.Theorems.AbstractGaloisConnection public
open import LogOS.LT.Theorems.Centering public
open import LogOS.LT.Theorems.BoundaryGauge public
open import LogOS.LT.Theorems.ContextApproximation public
open import LogOS.LT.Theorems.AbstractCohomology public
open import LogOS.LT.Theorems.CenteringQuote public
open import LogOS.LT.Effectivity public
