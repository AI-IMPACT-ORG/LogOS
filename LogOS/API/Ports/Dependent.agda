{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Ports.Dependent where

-- Dependent-first port entrypoints (ultralocal by default).
--
-- This module is intended as the “default” import surface for locality-facing
-- packs: meaning injection happens at dependent boundaries, and uniform
-- boundaries are treated as constant-family special cases inline.

open import LogOS.Ports.PhysicalSemantics.Core public using (DependentLocalSemantics; TwoStageDependentLocalSemantics)

open import LogOS.Ports.Locality.Core public using
  ( LocalBoundary
  ; LocalityPort
  ; localKernel
  )
open import LogOS.Ports.Locality.Laws public using (⊑loc→probe⊑)
open import LogOS.Ports.Locality.Lifts public using (pointwiseClosure)
open import LogOS.Ports.ConstantFamily public using (constLocalityPort)

-- Convenient dependent-first aliases (kept local to this module to avoid
-- polluting the global API surface with naming conflicts).
Boundary = LocalBoundary
Kernel = localKernel
pointwise = pointwiseClosure

open import LogOS.Ports.PhysicalTransformers public using
  ( pointwiseMap
  ; pointwiseMap-mono
  ; pointwiseEndoMap
  ; pointwiseEndoMap-mono
  ; pointwiseMap-preservesFlow
  ; pointwiseEndoMap-preservesFlow
  ; mkKernelHomFlow₂
  ; mkKernelHomFlow
  )

open import LogOS.Ports.RestrictedProduct public using
  ( AlmostAll
  ; Restricted
  ; AEAgree
  ; AETrivial
  ; AETrivial-id
  ; AETrivial-comp
  ; AEPreserves
  ; AEPreserves-id
  ; AEPreserves-comp
  ; restricted-map
  )
