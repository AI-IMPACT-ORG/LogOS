{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Frameworks.OOPS where

open import LogOS.Prelude

-- OOPS-style “optimal ordered problem solver” fits the library’s scheme story:
-- evolving solver states are a process, and problem families are inputs.
--
-- This module currently exposes the generic process/choice infrastructure.

open import LogOS.Computation.SchemeCategory public
  using
    ( Process
    ; Interface
    ; schemeFromInterface
    ; ProcessHom
    ; ProcessHomLax
    ; ProcessHomCost
    ; mapInterface
    ; mapInterfaceLax
    )

-- --------------------------------------------------------------------------
-- Concrete embedding into UniversalIR
-- --------------------------------------------------------------------------
-- Minimal, checked instantiation: a bounded PATask choice into the shared
-- UniversalIR process. This closes the interface without claiming an optimal
-- search semantics.

import LogOS.Packs.Agents.Frameworks.Core as Core
import LogOS.Packs.Agents.Frameworks.PATask as PATaskF
import LogOS.Packs.Agents.Frameworks.UniversalIR as U
import LogOS.UniversalIR.Schemes as US

open US using (Bounded)

OOPSTask : Set
OOPSTask = Bounded U.PATask

oopsInterface : Interface OOPSTask U.UProcess
oopsInterface = PATaskF.boundedLambdaInterface

oopsFramework : Core.Framework OOPSTask ℕ U.UProcess
oopsFramework = record { interface = oopsInterface }
