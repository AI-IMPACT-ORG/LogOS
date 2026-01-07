{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Physics.All where

-- Physics-of-information surfaces for the Agents laboratory.

open import LogOS.Packs.Complexity.PhysicsOfInformation public
open import LogOS.Domain.Complexity.MeasurementCapacity public
open import LogOS.Domain.Complexity.InfoProcessingBounds public
open import LogOS.Domain.Complexity.DataProcessingInequality public
module MaxwellAgent where
  open import LogOS.Packs.Agents.Physics.MaxwellAgent public
module LearningCost where
  open import LogOS.Packs.Agents.Physics.LearningCost public
