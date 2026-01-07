{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Arguments.Transformer where

-- Single entrypoint for the transformer-related developments in the Agents pack.
--
-- This module is intentionally a thin re-export surface so papers/docs can point
-- to one stable path.

module Formalization where
  open import LogOS.Packs.Agents.Arguments.TransformerFormalization public

module Bridge where
  open import LogOS.Packs.Agents.Arguments.TransformerBridge public

module Scaling where
  open import LogOS.Packs.Agents.Arguments.TransformerScaling public

module KolmogorovScaling where
  open import LogOS.Packs.Agents.Arguments.TransformerKolmogorovScaling public

module ScalingPipeline where
  open import LogOS.Packs.Agents.Arguments.TransformerScalingPipeline public
