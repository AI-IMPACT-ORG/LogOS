{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.Scaling where

-- Single entrypoint for scaling-law related developments (experimental).
-- Kept lightweight so docs/papers can reference one stable path.

module Laws where
  open import LogOS.Packs.Agents.Experimental.Arguments.ScalingLaws public

module Learning where
  open import LogOS.Packs.Agents.Experimental.Arguments.LearningScaling public

module Transformers where
  module TransformerScaling where
    open import LogOS.Packs.Agents.Experimental.Arguments.TransformerScaling public

  module TransformerScalingPipeline where
    open import LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline public
