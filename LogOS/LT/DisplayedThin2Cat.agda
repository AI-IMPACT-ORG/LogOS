{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.DisplayedThin2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Displayed thin 2-categories and their Σ-totalisation.
--
-- This is the minimal abstraction needed to make:
-- - contracts (LOG∂) a Σ-totalisation (category-of-elements-style; refinement inherited from the base), and
-- - flow-equipped kernels (LOGᶠ) a displayed structure with a single coherence
--   inequality (Flow-naturality),
-- definitional/structural rather than bespoke.
--
-- Important scope note:
-- this module is *not* a fibration/cleavage interface. It is port packaging:
-- displayed morphisms are extra obligations on 1-cells, and total morphism
-- refinement is inherited from the base thin 2-category only.
--
-- Engineering reading:
-- - displayed objects are per-component configuration (ports/guards/doctrines),
-- - displayed morphisms are per-adapter law/coherence obligations, and
-- - totalisation builds the “decorated component graph” with the same observable
--   refinement on underlying adapters.
--
-- Module-structure note:
-- auxiliary modules under `LogOS/LT/DisplayedThin2Cat/*.agda` exist only as
-- secondary navigation/anchor targets for documentation, and the implementation
-- is split across them.
--
-- This file remains the atomic LT spine surface (see `scripts/check/atomic_spine_import_check.sh`).

import LogOS.LT.DisplayedThin2Cat.Core as Core
import LogOS.LT.DisplayedThin2Cat.Totalisation as Total
import LogOS.LT.DisplayedThin2Cat.MapDecorated as Map
import LogOS.LT.DisplayedThin2Cat.Product as Product

open Core public using
  ( DisplayedThin2Cat
  ; Ob
  ; HomD
  ; idD
  ; compD
  ; LawDisplayed
  ; LawDisplayedOn
  )

open Total public using
  ( TotalObj
  ; base
  ; disp
  ; TotalObjR
  ; mkTotalObjR
  ; toTotalObjR
  ; fromTotalObjR
  ; TotalHom
  ; baseHom
  ; dispHom
  ; TotalHomR
  ; mkTotalHomR
  ; toTotalHomR
  ; fromTotalHomR
  ; TotalHomPreorder
  ; total⊑→base⊑
  ; base⊑→total⊑
  ; total≈→base≈
  ; base≈→total≈
  ; baseHom≡→total≈
  ; byBaseHom≡
  ; TotalThin2Cat
  ; forgetTotal
  ; DecoratedObj
  ; DecoratedHom
  ; DecoratedHomPreorder
  ; DecoratedThin2Cat
  ; forgetDecorated
  )

open Map public using (mapDecorated)

open Product public using
  ( ProductDisplayed
  ; DisplayedCat
  ; forgetProductLeft
  ; forgetProductRight
  )
