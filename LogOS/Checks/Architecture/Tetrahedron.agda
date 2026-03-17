{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Checks.Architecture.Tetrahedron where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; _≈_)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
import LogOS.LT.Thin2Functor as Thin2Functor
open import LogOS.LT.Thin2Functor using (mapObj; mapHom)
import LogOS.LT.LOG.Kernel2Cat as Kernel2Cat
import LogOS.LT.Hom.Core as Hom
import LogOS.LT.Architecture.Apex as Apex
import LogOS.LT.Architecture.Definitional as ArchitectureDefinitional
import LogOS.LT.Architecture.Face as Face
import LogOS.LT.Architecture.Tetrahedron as Tetrahedron
import LogOS.API.LT as DefaultAPI
import LogOS.Ports.PhysicalSemantics.Core as Physical
import LogOS.Ports.Realisations.DependentStack as R
import LogOS.Ports.Realisations.Architecture as Architecture

module GenericTetrahedronLaws {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
  (S : Physical.DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}) where

  T : Tetrahedron.Tetrahedron
  T = Architecture.logOSTetrahedron {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S

  construction-id≈
    : ∀ {A}
    → _≈_
        (Thin2Cat.Hom (Tetrahedron.Equator T)
          (mapObj (Tetrahedron.forgetConstruction T) A)
          (mapObj (Tetrahedron.forgetConstruction T) A))
        (mapHom (Tetrahedron.forgetConstruction T)
          (Thin2Cat.id (Tetrahedron.constructionApex T) {A}))
        (Thin2Cat.id (Tetrahedron.Equator T)
          {A = mapObj (Tetrahedron.forgetConstruction T) A})
  construction-id≈ {A = A} =
    Apex.forget-id≈ (Tetrahedron.Construction T) {X = A}

  construction-comp≈
    : ∀ {A B C}
      (f : Con (Thin2Cat.Hom (Tetrahedron.constructionApex T) B C))
      (g : Con (Thin2Cat.Hom (Tetrahedron.constructionApex T) A B))
    → _≈_
        (Thin2Cat.Hom (Tetrahedron.Equator T)
          (mapObj (Tetrahedron.forgetConstruction T) A)
          (mapObj (Tetrahedron.forgetConstruction T) C))
        (mapHom (Tetrahedron.forgetConstruction T)
          (Thin2Cat._∘_ (Tetrahedron.constructionApex T) f g))
        (Thin2Cat._∘_ (Tetrahedron.Equator T)
          (mapHom (Tetrahedron.forgetConstruction T) f)
          (mapHom (Tetrahedron.forgetConstruction T) g))
  construction-comp≈ {A = A} {B = B} {C = C} f g =
    Apex.forget-comp≈ (Tetrahedron.Construction T) {X = A} {Y = B} {Z = C} f g

  discipline-id≈
    : ∀ {A}
    → _≈_
        (Thin2Cat.Hom (Tetrahedron.Equator T)
          (mapObj (Tetrahedron.forgetDiscipline T) A)
          (mapObj (Tetrahedron.forgetDiscipline T) A))
        (mapHom (Tetrahedron.forgetDiscipline T)
          (Thin2Cat.id (Tetrahedron.disciplineApex T) {A}))
        (Thin2Cat.id (Tetrahedron.Equator T)
          {A = mapObj (Tetrahedron.forgetDiscipline T) A})
  discipline-id≈ {A = A} =
    Apex.forget-id≈ (Tetrahedron.Discipline T) {X = A}

  discipline-comp≈
    : ∀ {A B C}
      (f : Con (Thin2Cat.Hom (Tetrahedron.disciplineApex T) B C))
      (g : Con (Thin2Cat.Hom (Tetrahedron.disciplineApex T) A B))
    → _≈_
        (Thin2Cat.Hom (Tetrahedron.Equator T)
          (mapObj (Tetrahedron.forgetDiscipline T) A)
          (mapObj (Tetrahedron.forgetDiscipline T) C))
        (mapHom (Tetrahedron.forgetDiscipline T)
          (Thin2Cat._∘_ (Tetrahedron.disciplineApex T) f g))
        (Thin2Cat._∘_ (Tetrahedron.Equator T)
          (mapHom (Tetrahedron.forgetDiscipline T) f)
          (mapHom (Tetrahedron.forgetDiscipline T) g))
  discipline-comp≈ {A = A} {B = B} {C = C} f g =
    Apex.forget-comp≈ (Tetrahedron.Discipline T) {X = A} {Y = B} {Z = C} f g

  realisation-id≈
    : ∀ {A}
    → _≈_
        (Thin2Cat.Hom (Tetrahedron.Equator T)
          (mapObj (Tetrahedron.forgetRealisation T) A)
          (mapObj (Tetrahedron.forgetRealisation T) A))
        (mapHom (Tetrahedron.forgetRealisation T)
          (Thin2Cat.id (Tetrahedron.realisationApex T) {A}))
        (Thin2Cat.id (Tetrahedron.Equator T)
          {A = mapObj (Tetrahedron.forgetRealisation T) A})
  realisation-id≈ {A = A} =
    Apex.forget-id≈ (Tetrahedron.Realisation T) {X = A}

  realisation-comp≈
    : ∀ {A B C}
      (f : Con (Thin2Cat.Hom (Tetrahedron.realisationApex T) B C))
      (g : Con (Thin2Cat.Hom (Tetrahedron.realisationApex T) A B))
    → _≈_
        (Thin2Cat.Hom (Tetrahedron.Equator T)
          (mapObj (Tetrahedron.forgetRealisation T) A)
          (mapObj (Tetrahedron.forgetRealisation T) C))
        (mapHom (Tetrahedron.forgetRealisation T)
          (Thin2Cat._∘_ (Tetrahedron.realisationApex T) f g))
        (Thin2Cat._∘_ (Tetrahedron.Equator T)
          (mapHom (Tetrahedron.forgetRealisation T) f)
          (mapHom (Tetrahedron.forgetRealisation T) g))
  realisation-comp≈ {A = A} {B = B} {C = C} f g =
    Apex.forget-comp≈ (Tetrahedron.Realisation T) {X = A} {Y = B} {Z = C} f g

  bipyramid : Face.ArchitectureFace
  bipyramid = Tetrahedron.bipyramidFace T

  hexagonal : Face.ArchitectureFace
  hexagonal = Tetrahedron.hexagonalFace T

  sharedBoundary : Face.ArchitectureFace
  sharedBoundary = Tetrahedron.sharedBoundaryFace T

module GenericRealisationSurface {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
  {S : Physical.DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
  (F : R.RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S) where

  realisation-forget≡
    : Apex.forget
        (Architecture.realisationApexOver {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} {S = S})
      ≡ Thin2Functor.forgetPullbackThin2Functor
          {C = Kernel2Cat.LOG
                 {ℓI ⊔ ℓOCon}
                 {ℓI ⊔ ℓORel}
                 {ℓCode = ℓOp ⊔ ℓCode}}
          (R.RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
          R.StackKOf
  realisation-forget≡ =
    ArchitectureDefinitional.forget-pullbackApexOver≡
      (R.RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
      R.StackKOf

  denoteStackWitness
    : Hom.KernelHom (R.StackKOf F) (Architecture.DenoteK F)
  denoteStackWitness = Architecture.denoteStack F

  denoteProgramWitness
    : Hom.KernelHom (R.ProgramKOf F) (Architecture.DenoteK F)
  denoteProgramWitness = Architecture.denoteProgram F

module DefaultCuratedSurface {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
  (S : Physical.DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}) where

  tetrahedron : DefaultAPI.Tetrahedron
  tetrahedron = Architecture.logOSTetrahedron {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S

  hexagonal : DefaultAPI.ArchitectureFace
  hexagonal = DefaultAPI.logOSHexagonalFace {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S
