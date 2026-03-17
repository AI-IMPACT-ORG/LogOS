{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Architecture.Tetrahedron where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Primary typed architecture package:
-- one shared equator, three forgetful apices, and derived two-apex faces.

open import LogOS.Prelude
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.Architecture.Apex using (ApexOver; Apex; forget)
open import LogOS.LT.Architecture.Face using (ArchitectureFace)

record Tetrahedron : Setω where
  field
    ℓObjE : Level
    ℓHomConE : Level
    ℓHomRelE : Level

    Equator : Thin2Cat ℓObjE ℓHomConE ℓHomRelE

    Construction : ApexOver Equator
    Discipline : ApexOver Equator
    Realisation : ApexOver Equator

open Tetrahedron public

constructionApex
  : (T : Tetrahedron)
  → Thin2Cat (ApexOver.ℓObjA (Construction T)) (ApexOver.ℓHomConA (Construction T)) (ApexOver.ℓHomRelA (Construction T))
constructionApex T = Apex (Construction T)

disciplineApex
  : (T : Tetrahedron)
  → Thin2Cat (ApexOver.ℓObjA (Discipline T)) (ApexOver.ℓHomConA (Discipline T)) (ApexOver.ℓHomRelA (Discipline T))
disciplineApex T = Apex (Discipline T)

realisationApex
  : (T : Tetrahedron)
  → Thin2Cat (ApexOver.ℓObjA (Realisation T)) (ApexOver.ℓHomConA (Realisation T)) (ApexOver.ℓHomRelA (Realisation T))
realisationApex T = Apex (Realisation T)

forgetConstruction : (T : Tetrahedron) → Thin2Functor (constructionApex T) (Equator T)
forgetConstruction T = forget (Construction T)

forgetDiscipline : (T : Tetrahedron) → Thin2Functor (disciplineApex T) (Equator T)
forgetDiscipline T = forget (Discipline T)

forgetRealisation : (T : Tetrahedron) → Thin2Functor (realisationApex T) (Equator T)
forgetRealisation T = forget (Realisation T)

bipyramidFace : Tetrahedron → ArchitectureFace
bipyramidFace T =
  record
    { ℓObjE = ℓObjE T
    ; ℓHomConE = ℓHomConE T
    ; ℓHomRelE = ℓHomRelE T
    ; Equator = Equator T
    ; Left = Construction T
    ; Right = Discipline T
    }

hexagonalFace : Tetrahedron → ArchitectureFace
hexagonalFace T =
  record
    { ℓObjE = ℓObjE T
    ; ℓHomConE = ℓHomConE T
    ; ℓHomRelE = ℓHomRelE T
    ; Equator = Equator T
    ; Left = Discipline T
    ; Right = Realisation T
    }

sharedBoundaryFace : Tetrahedron → ArchitectureFace
sharedBoundaryFace T =
  record
    { ℓObjE = ℓObjE T
    ; ℓHomConE = ℓHomConE T
    ; ℓHomRelE = ℓHomRelE T
    ; Equator = Equator T
    ; Left = Construction T
    ; Right = Realisation T
    }
