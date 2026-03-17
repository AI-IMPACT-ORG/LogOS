{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Ports.LTStrictificationLOG where

-- Explicit strictification surface for LOG-basis law ports.
--
-- Import this module only when strict decode laws or antisymmetry-driven
-- collapse are part of the intended semantics.

open import LogOS.LT.DisplayedThin2Cat public

import LogOS.LT.LOG.ClassicalLimit2Cat as ClassicalLimit
import LogOS.LT.LOG.StrictDecode2Cat as StrictDecode
import LogOS.LT.Ports.PortStack.ClassicalLimit as Stack

open import LogOS.LT.LOG.Discipline.StrictificationAsDisplayed public
  renaming (ok to ltStrictificationAsDisplayed-ok)
