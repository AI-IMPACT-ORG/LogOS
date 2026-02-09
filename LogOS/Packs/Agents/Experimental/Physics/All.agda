{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Physics.All where

-- Physics-of-information surfaces for the Agents laboratory (experimental).

open import LogOS.Packs.Complexity.Experimental.PhysicsOfInformation public
open import LogOS.Complexity.MeasurementCapacity public
open import LogOS.Complexity.InfoProcessingBounds public
open import LogOS.Complexity.DataProcessingInequality public
module MaxwellAgent where
  open import LogOS.Packs.Agents.Experimental.Physics.MaxwellAgent public
module LearningCost where
  open import LogOS.Packs.Agents.Experimental.Physics.LearningCost public
