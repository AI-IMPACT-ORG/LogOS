{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Strict2Cat where

-- MetaTheory — Strict 2-category presentations (non-unique bases).
--
-- LogOS alignment:
-- - `TwoCellOps` is the stable *basis* interface consumed by the LT spine.
-- - “Literature presentations” of (strict) 2-categories are builders for that
--   basis, plus explicit law bundles.
--
-- Refinement stance:
-- - strict equalities live in S-tier and are only used to *construct* 2-cells
--   (G-tier laws up to mutual 2-cell/refinement).

import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Strict2Cat.PresentationW as W
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Strict2Cat.PresentationH as H
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Strict2Cat.TranslateHtoW as T

open W public using
  ( Strict2CatWLaws
  ; Strict2CatW
  ; Strict2CatW→TwoCellOps
  ; Strict2CatW→TwoCellOpsLaws
  ; Strict2CatW→Thin2Cat
  ; Strict2CatW→Thin2CatLaws
  )

open H public using
  ( Strict2CatHOps
  ; Strict2CatHLaws
  ; Strict2CatH
  ; Strict2CatH→TwoCellOps
  ; Strict2CatH→TwoCellOpsLaws
  ; Strict2CatH→Thin2Cat
  ; Strict2CatH→Thin2CatLaws
  )

open T public using (Strict2CatH→W)
