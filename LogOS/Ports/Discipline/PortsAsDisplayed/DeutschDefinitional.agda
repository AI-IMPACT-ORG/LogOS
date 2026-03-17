{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Discipline.PortsAsDisplayed.DeutschDefinitional where

-- The historical reversible+Landauer wrapper has been deleted.
-- The remaining optional physical definitional equalities live in the generic
-- Landauer and prequantum lanes.

import LogOS.Ports.AbstractLandauer2Cat.Definitional as LandauerDef

open LandauerDef public using
  ( WithLandauer-def
  ; forgetLandauer-def
  )
