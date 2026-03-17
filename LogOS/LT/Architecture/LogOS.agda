{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Architecture.LogOS where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Canonical LT-layer architecture faces over the preserved façade `LOG`.
--
-- Reading:
-- - construction apex: stacks reindexed into `LOG` by `stackKernel`
-- - discipline apex: architecture+implementation totalisation `LOGᴳʳ`
-- - derived bi-pyramid face: construction + discipline
--
-- Equality-bearing reindexing helpers along `toLOG` stay in the explicit
-- strictification lane `LogOS.LT.LOG.PortReindexing.Strictification`.

open import LogOS.Prelude
open import LogOS.LT.Architecture.Apex using (ApexOver; pullbackApexOver)
open import LogOS.LT.Architecture.Face using (ArchitectureFace)

import LogOS.LT.Stack.Core as LTStack
import LogOS.LT.Stack.Program as LTProgram

import LogOS.LT.LOG.Kernel2Cat.Core as Kernel2Cat
import LogOS.LT.LOG.Implementation2Cat.Core as Implementation2Cat
import LogOS.LT.LOG.PortReindexing as KernelFaces

stackApexOver
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level}
  → ApexOver (Kernel2Cat.LOG {ℓB} {ℓRel} {ℓCode = ℓOp ⊔ ℓCode})
stackApexOver {ℓB} {ℓRel} {ℓOp} {ℓCode} =
  pullbackApexOver
    {E = Kernel2Cat.LOG {ℓB} {ℓRel} {ℓCode = ℓOp ⊔ ℓCode}}
    (LTStack.Stack {ℓB} {ℓRel} {ℓOp} {ℓCode})
    LTStack.stackKernel

disciplineApexOver
  : ∀ {ℓB ℓRel ℓCode : Level}
  → ApexOver (Kernel2Cat.LOG {ℓB} {ℓRel} {ℓCode})
disciplineApexOver {ℓB} {ℓRel} {ℓCode} =
  record
    { ℓObjA = lsuc (ℓB ⊔ ℓRel ⊔ ℓCode)
    ; ℓHomConA = lsuc ℓB ⊔ lsuc ℓRel ⊔ ℓCode ⊔ ℓRel
    ; ℓHomRelA = ℓB ⊔ ℓRel
    ; Apex = Implementation2Cat.LOGᴳʳ {ℓB} {ℓRel} {ℓCode}
    ; forget = Implementation2Cat.toLOG {ℓB} {ℓRel} {ℓCode}
    }

logOSBiPyramid
  : ∀ {ℓB ℓRel ℓOp ℓCode : Level}
  → ArchitectureFace
logOSBiPyramid {ℓB} {ℓRel} {ℓOp} {ℓCode} =
  record
    { ℓObjE = lsuc (ℓB ⊔ ℓRel ⊔ (ℓOp ⊔ ℓCode))
    ; ℓHomConE = lsuc ℓB ⊔ lsuc ℓRel ⊔ (ℓOp ⊔ ℓCode)
    ; ℓHomRelE = ℓOp ⊔ ℓCode ⊔ ℓRel
    ; Equator = Kernel2Cat.LOG {ℓB} {ℓRel} {ℓCode = ℓOp ⊔ ℓCode}
    ; Left = stackApexOver {ℓB} {ℓRel} {ℓOp} {ℓCode}
    ; Right = disciplineApexOver {ℓB} {ℓRel} {ℓCode = ℓOp ⊔ ℓCode}
    }

open KernelFaces public using
  ( kernelOfToLOG
  )

open LTProgram public using (programKernel)
