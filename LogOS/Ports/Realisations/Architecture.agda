{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Realisations.Architecture where

-- One-boundary / many-realisations as an actual architecture corner.
--
-- Once a dependent-local semantics ledger `S` is fixed, each
-- `RealisationFamily S` is:
-- - a shared-boundary stack (`stackOf` / `StackKOf` / `ProgramKOf`), and
-- - therefore an apex over the preserved façade `LOG`.
--
-- The canonical denotation surface into boundary-as-code is definitional on the
-- chosen family `F`; it is not hidden behind an extra ledger/deck wrapper.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; refl⊑)
open import LogOS.LT.Architecture.Apex using (ApexOver; pullbackApexOver)
open import LogOS.LT.Architecture.Face using (ArchitectureFace)
open import LogOS.LT.Architecture.LogOS as LTArchitecture using (stackApexOver; disciplineApexOver)
open import LogOS.LT.Architecture.Tetrahedron using (Tetrahedron; bipyramidFace; hexagonalFace; sharedBoundaryFace)
open import LogOS.LT.Kernel using (Kernel; decode)
open import LogOS.LT.Hom.Core using (KernelHom)
open import LogOS.LT.HomFlow using (KernelHomFlow)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)

open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)
import LogOS.Ports.Realisations.DependentStack as R
open import LogOS.Ports.BoundaryAsCode as Denote using (boundaryKernel; denote; denoteFlow)

realisationApexOver
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
  → ApexOver
      (LOG {ℓI ⊔ ℓOCon} {ℓI ⊔ ℓORel} {ℓCode = ℓOp ⊔ ℓCode})
realisationApexOver {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} {S} =
  pullbackApexOver
    {E = LOG {ℓI ⊔ ℓOCon} {ℓI ⊔ ℓORel} {ℓCode = ℓOp ⊔ ℓCode}}
    (R.RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
    R.StackKOf

DenoteK
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
  → (F : R.RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
  → Kernel (ℓI ⊔ ℓOCon) (ℓI ⊔ ℓORel) (ℓI ⊔ ℓOCon)
DenoteK {S = S} _ =
  Denote.boundaryKernel (DependentLocalSemantics.I S) (DependentLocalSemantics.O S)

denoteOp
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
    (F : R.RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
  → (o : R.OpOf F)
  → KernelHom (R.localKOf F o) (DenoteK F)
denoteOp F o = Denote.denote (R.localOf F o)

denoteOpFlow
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
    (F : R.RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
  → (o : R.OpOf F)
  → KernelHomFlow (DependentLocalSemantics.GC S) (DependentLocalSemantics.GC S) (denoteOp F o)
denoteOpFlow {S = S} F o =
  Denote.denoteFlow (DependentLocalSemantics.GC₀ S) (R.localOf F o)

decodeDenotation
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode ℓCodeₖ : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
    (F : R.RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
    {Codeₖ : Set ℓCodeₖ}
  → (decodeₖ : Codeₖ → Con (DependentLocalSemantics.Bnd S))
  → KernelHom
      (record
        { bnd = DependentLocalSemantics.Bnd S
        ; Code = Codeₖ
        ; decode = decodeₖ
        })
      (DenoteK F)
decodeDenotation {ℓI} {ℓOCon} {S = S} F decodeₖ =
  Denote.decodeDenotation
    {I = DependentLocalSemantics.I S}
    {O = DependentLocalSemantics.O S}
    decodeₖ

decodeDenotationFlow
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode ℓCodeₖ : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
    (F : R.RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
    {Codeₖ : Set ℓCodeₖ}
    (decodeₖ : Codeₖ → Con (DependentLocalSemantics.Bnd S))
  → KernelHomFlow
      (DependentLocalSemantics.GC S)
      (DependentLocalSemantics.GC S)
      (decodeDenotation F decodeₖ)
decodeDenotationFlow {S = S} F decodeₖ =
  record { preserves-Flow = λ _ → refl⊑ (DependentLocalSemantics.Bnd S) }

denoteStack
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
    (F : R.RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
  → KernelHom (R.StackKOf F) (DenoteK F)
denoteStack F = decodeDenotation F (decode (R.StackKOf F))

denoteStackFlow
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
    (F : R.RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
  → KernelHomFlow (DependentLocalSemantics.GC S) (DependentLocalSemantics.GC S) (denoteStack F)
denoteStackFlow F = decodeDenotationFlow F (decode (R.StackKOf F))

denoteProgram
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
    (F : R.RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
  → KernelHom (R.ProgramKOf F) (DenoteK F)
denoteProgram F = decodeDenotation F (decode (R.ProgramKOf F))

denoteProgramFlow
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    {S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}}
    (F : R.RealisationFamily {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
  → KernelHomFlow (DependentLocalSemantics.GC S) (DependentLocalSemantics.GC S) (denoteProgram F)
denoteProgramFlow F = decodeDenotationFlow F (decode (R.ProgramKOf F))

logOSTetrahedron
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    (S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
  → Tetrahedron
logOSTetrahedron {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S =
  record
    { ℓObjE = lsuc ((ℓI ⊔ ℓOCon) ⊔ (ℓI ⊔ ℓORel) ⊔ (ℓOp ⊔ ℓCode))
    ; ℓHomConE = lsuc (ℓI ⊔ ℓOCon) ⊔ lsuc (ℓI ⊔ ℓORel) ⊔ (ℓOp ⊔ ℓCode)
    ; ℓHomRelE = (ℓOp ⊔ ℓCode) ⊔ (ℓI ⊔ ℓORel)
    ; Equator = LOG {ℓI ⊔ ℓOCon} {ℓI ⊔ ℓORel} {ℓCode = ℓOp ⊔ ℓCode}
    ; Construction =
        LTArchitecture.stackApexOver
          {ℓB = ℓI ⊔ ℓOCon}
          {ℓRel = ℓI ⊔ ℓORel}
          {ℓOp = ℓOp}
          {ℓCode = ℓCode}
    ; Discipline =
        LTArchitecture.disciplineApexOver
          {ℓB = ℓI ⊔ ℓOCon}
          {ℓRel = ℓI ⊔ ℓORel}
          {ℓCode = ℓOp ⊔ ℓCode}
    ; Realisation = realisationApexOver {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} {S = S}
    }

logOSBipyramidFace
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    (S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
  → ArchitectureFace
logOSBipyramidFace {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S =
  bipyramidFace (logOSTetrahedron {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)

logOSHexagonalFace
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    (S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
  → ArchitectureFace
logOSHexagonalFace {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S =
  hexagonalFace (logOSTetrahedron {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)

logOSSharedBoundaryFace
  : ∀ {ℓI ℓOCon ℓORel ℓOp ℓCode : Level}
    (S : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel})
  → ArchitectureFace
logOSSharedBoundaryFace {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S =
  sharedBoundaryFace (logOSTetrahedron {ℓI} {ℓOCon} {ℓORel} {ℓOp} {ℓCode} S)
