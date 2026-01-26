{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Socket.FromLogicCore where

open import LogOS.Prelude

open import LogOS.Minimal.Adapter using (QAdapter)

open import LogOS.API.Assumptions.Core using (LogicCore)
import LogOS.Packs.Agents.Socket.FromLogicKernel as FromLK

-- Bridge: build an agent socket directly from a shared `LogicCore`.
--
-- This keeps pack composition “bundle-first”: you choose one `LogicCore`
-- instance, then build agents/ports/contracts against its kernel interface.

-- Default step grade is `QAdapter.e` (the unit grade embedded into the scale).
-- Use `ForStepGrade` if you want to choose a different step grade (e.g. from a
-- `UniversalityBundle`).
module For
  {ℓ ℓTask : Level}
  (C : LogicCore {ℓ})
  (Task : Set ℓTask)
  where

  module Base = FromLK.For (LogicCore.K C) (QAdapter.e (LogicCore.Q C)) Task

  open Base public using (mkCodeSocket; mkBoundarySocket)

module ForStepGrade
  {ℓ ℓTask : Level}
  (C : LogicCore {ℓ})
  (stepGrade : QAdapter.Scale (LogicCore.Q C))
  (Task : Set ℓTask)
  where

  module Base = FromLK.For (LogicCore.K C) stepGrade Task

  open Base public using (mkCodeSocket; mkBoundarySocket)
