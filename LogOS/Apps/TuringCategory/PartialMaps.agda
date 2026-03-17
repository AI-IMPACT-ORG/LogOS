{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.PartialMaps where

-- Canonical “classical” partial maps as a Kleisli-style thin 2-category.
--
-- Objects: `ConPreorder` (fixed universe parameters).
-- Morphisms X ⇀ Y: monotone maps `Con X → Lift (Con Y)`.
-- 2-cells: pointwise refinement.
--
-- This module is intended as the ZFC-friendly semantic target for
-- extensional/partial-map readings.

import LogOS.Apps.TuringCategory.PartialMaps.Core as Core
import LogOS.Apps.TuringCategory.PartialMaps.Cartesian as Cartesian

open Core public using
  ( PartialMap
  ; map
  ; mono
  ; _∘p_
  ; idp
  ; PartialMapPreorder
  ; Par
  ; Par-id-left
  ; Par-id-right
  ; Par-assoc
  ; ParLaws
  )

open Cartesian public using
  ( UnitCP
  ; !
  ; π₁
  ; π₂
  ; ⟨_,_⟩
  )
