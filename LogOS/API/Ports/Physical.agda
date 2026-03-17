{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Ports.Physical where

-- Curated observational and shared-semantics port surfaces.
--
-- Includes locality, boundary-as-code, shared distributed semantics tooling,
-- and physical observational bridges.
-- Optional doctrine packs (Landauer / Deutsch / no-cloning) live in
-- `LogOS.API.Ports.PhysicalOptional` so the default physical shell records
-- the core observational discipline without pulling the heavier optional lane
-- into every curated import.
-- Physics, opacity, and irreversibility are intentionally small layered
-- slices of this same port discipline, not separate port architectures.
-- Residuals and Metamath remain available below as explicit submodules rather
-- than part of the top-level physical narrative.

open import LogOS.Ports.IO public
open import LogOS.LT.ConPreorder.Isomorphism public using
  ( OrderIso
  ; f
  ; g
  ; f-mono
  ; g-mono
  ; fg≈id
  ; gf≈id
  ; mono-≈
  ; idOrderIso
  ; compOrderIso
  ; orderIso-reflects-≈
  ; collapse-obstructs-orderIso
  )

open import LogOS.Ports.BoundaryAsCode public using
  ( BoundaryCode
  ; boundaryPort
  ; boundaryKernel
  ; denote
  ; denoteFlow
  ; TransparentDenotationPackage
  ; TransparentDenotationPackage≈
  ; canonicalTransparentDenotationPackage
  ; transparentDenotationFiber
  ; transparentDenotationNoFork
  ; normalisedTransparentCode
  ; transparentDenotation≈denote
  ; transparentDenotation↔localCodePreorder
  ; transparentDenotation≈localCodePreorder
  ; transparent-mapCode≈decode
  ; transparent-mapCode-normalised≈decode
  ; transparent-mapCode-unique≈
  )

open import LogOS.Ports.Locality.Core public using
  ( LocalBoundary
  ; LocalityPort
  ; localKernel
  )
open import LogOS.Ports.Locality.Lifts public using (pointwiseClosure)
open import LogOS.Ports.Causality public

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

open import LogOS.Ports.BoundaryTransparency public using
  ( BoundaryTransparent
  ; transportCon
  ; untransportCon
  ; idBoundaryTransparent
  ; compBoundaryTransparent
  )

open import LogOS.Ports.PhysicalSemantics.Core public using (DependentLocalSemantics; TwoStageDependentLocalSemantics)
open import LogOS.Ports.Valuation.QAdapter public using (QAdapter)
open import LogOS.Ports.PhysicalTransformers public using
  ( pointwiseMap-preservesFlow
  ; pointwiseEndoMap-preservesFlow
  ; mkKernelHomFlow₂
  ; mkKernelHomFlow
  )

import LogOS.Ports.Residuals as Residuals
import LogOS.Ports.Metamath as Metamath
