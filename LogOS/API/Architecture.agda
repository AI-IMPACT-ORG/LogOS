{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Architecture where

-- Curated tetrahedral local-refinement architecture surface.
--
-- This module is explanatory infrastructure:
-- it re-exports typed packaging for the repository’s recurring architecture
-- shape (equator + forgetful apices + derived faces), together with the
-- canonical LT and shared-boundary realisation instances.
--
-- Policy note:
-- `LogOS/API/**` stays within Prelude/Syntax/LT/Ports/API layers (no Apps/Adapters).
-- Constructor equalities are intentionally quarantined under
-- `LogOS.LT.Architecture.Definitional` and do not belong to this public lane.

open import LogOS.LT.Architecture.Apex public using
  ( ApexOver
  ; pullbackApexOver
  ; displayedApexOver
  ; forget-id≈
  ; forget-comp≈
  )
open import LogOS.LT.Architecture.Face public using
  ( ArchitectureFace
  ; leftApex
  ; rightApex
  ; forgetLeft
  ; forgetRight
  )
open import LogOS.LT.Architecture.Tetrahedron public using
  ( Tetrahedron
  ; constructionApex
  ; disciplineApex
  ; realisationApex
  ; forgetConstruction
  ; forgetDiscipline
  ; forgetRealisation
  ; bipyramidFace
  ; hexagonalFace
  ; sharedBoundaryFace
  )
open import LogOS.LT.Architecture.LogOS public using
  ( stackApexOver
  ; disciplineApexOver
  ; logOSBiPyramid
  )
open import LogOS.Ports.Realisations.Architecture public using
  ( realisationApexOver
  ; DenoteK
  ; denoteOp
  ; denoteOpFlow
  ; decodeDenotation
  ; decodeDenotationFlow
  ; denoteStack
  ; denoteStackFlow
  ; denoteProgram
  ; denoteProgramFlow
  ; logOSTetrahedron
  ; logOSBipyramidFace
  ; logOSHexagonalFace
  ; logOSSharedBoundaryFace
  )
open import LogOS.LT.Architecture.BiPyramid public using (BiPyramid)

module Equator where
  -- Preserved observational comparison world.
  open import LogOS.LT.LOG.Kernel2Cat public

module Discipline where
  -- Architecture-first basis + displayed implementation totalisation.
  open import LogOS.LT.LOG.Boundary2Cat public
  open import LogOS.LT.LOG.Implementation2Cat public

  -- Displayed/Σ-totalised authoring spine.
  open import LogOS.LT.DisplayedThin2Cat public

  -- Port stack infrastructure and templates.
  open import LogOS.LT.Ports.PortSig public using
    ( PortSig
    ; PortEntry
    ; mkPortEntry
    ; mkEntry
    ; sig
    ; TagTy
    ; Tagℓ
    )
  open import LogOS.LT.Ports.Template.Singleton2Cat public using (Singleton2Cat; mkSingleton2Cat)
  open import LogOS.LT.Ports.Template.LawSingleton2Cat public
  open import LogOS.LT.Ports.Template.Stack2Cat public using (Stack2Cat; mkStack2Cat)

module Construction where
  -- Stacks and the optional program/macro layer (construction apex tooling).
  open import LogOS.LT.Stack public

module Faces where
  -- Derived two-apex views and their canonical realisation-specialised faces.
  -- Equality-based reindexing/weakenings live under `LogOS.API.Strictification`.
  open import LogOS.LT.Architecture.BiPyramid public using
    ( BiPyramid
    ; constructionApex
    ; disciplineApex
    ; forgetConstruction
    ; forgetDiscipline
    )
  open import LogOS.LT.Architecture.Tetrahedron public using
    ( bipyramidFace
    ; hexagonalFace
    ; sharedBoundaryFace
    )
  open import LogOS.Ports.Realisations.Architecture public using
    ( logOSBipyramidFace
    ; logOSHexagonalFace
    ; logOSSharedBoundaryFace
    )
  open import LogOS.LT.LOG.PortReindexing public using (kernelOfToLOG)

module Capstones where
  -- Facet theorem bundles over the LT spine.
  --
  -- Repository-level capstone (`MechanisableLogicWorld`) lives under
  -- `LogOS/Apps/LogicArchitecture/MetaTheory/Basis/FoundationalLogic.agda` and
  -- is intentionally not re-exported from `LogOS.API.*` by layer policy.
  open import LogOS.LT.Theorems.ArchitecturalNormalForm public

module Realisation where
  -- Shared-boundary / many-realisations authoring surface.
  open import LogOS.Ports.Realisations.DependentStack public
  open import LogOS.Ports.Realisations.Architecture public
