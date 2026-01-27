{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.Transformer where

-- Single entrypoint for the transformer-related developments in the Agents pack.
--
-- This module is intentionally a lightweight re-export surface so papers/docs can point
-- to one stable path.

module Formalization where
  open import LogOS.Packs.Agents.Experimental.Arguments.TransformerFormalization public

module Bridge where
  open import LogOS.Packs.Agents.Experimental.Arguments.TransformerBridge public

module Scaling where
  open import LogOS.Packs.Agents.Experimental.Arguments.TransformerScaling public

module KolmogorovScaling where
  open import LogOS.Packs.Agents.Experimental.Arguments.TransformerKolmogorovScaling public

module ScalingPipeline where
  open import LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline public
