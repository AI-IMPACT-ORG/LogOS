{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Physics.All where

-- Physics-of-information surfaces for the Agents laboratory (experimental).

open import LogOS.Packs.Complexity.Experimental.PhysicsOfInformation public
open import LogOS.Domain.Complexity.MeasurementCapacity public
open import LogOS.Domain.Complexity.InfoProcessingBounds public
open import LogOS.Domain.Complexity.DataProcessingInequality public
module MaxwellAgent where
  open import LogOS.Packs.Agents.Experimental.Physics.MaxwellAgent public
module LearningCost where
  open import LogOS.Packs.Agents.Experimental.Physics.LearningCost public
