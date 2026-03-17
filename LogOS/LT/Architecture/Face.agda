{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Architecture.Face where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Neutral two-apex face over one shared equator.
--
-- This is the generic typed shape behind derived named views such as the
-- bi-pyramid face and the hexagonal face.

open import LogOS.Prelude
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.Architecture.Apex using (ApexOver; Apex; forget)

record ArchitectureFace : Setω where
  field
    ℓObjE : Level
    ℓHomConE : Level
    ℓHomRelE : Level

    Equator : Thin2Cat ℓObjE ℓHomConE ℓHomRelE

    Left : ApexOver Equator
    Right : ApexOver Equator

open ArchitectureFace public

leftApex
  : (F : ArchitectureFace)
  → Thin2Cat (ApexOver.ℓObjA (Left F)) (ApexOver.ℓHomConA (Left F)) (ApexOver.ℓHomRelA (Left F))
leftApex F = Apex (Left F)

rightApex
  : (F : ArchitectureFace)
  → Thin2Cat (ApexOver.ℓObjA (Right F)) (ApexOver.ℓHomConA (Right F)) (ApexOver.ℓHomRelA (Right F))
rightApex F = Apex (Right F)

forgetLeft : (F : ArchitectureFace) → Thin2Functor (leftApex F) (Equator F)
forgetLeft F = forget (Left F)

forgetRight : (F : ArchitectureFace) → Thin2Functor (rightApex F) (Equator F)
forgetRight F = forget (Right F)
