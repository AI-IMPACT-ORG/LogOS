{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Architecture.BiPyramid where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Derived construction/discipline face view over the primary tetrahedral
-- architecture package.

import LogOS.LT.Architecture.Face as Face

open Face public renaming
  ( ArchitectureFace to BiPyramid
  ; Left to Construction
  ; Right to Discipline
  ; leftApex to constructionApex
  ; rightApex to disciplineApex
  ; forgetLeft to forgetConstruction
  ; forgetRight to forgetDiscipline
  )
