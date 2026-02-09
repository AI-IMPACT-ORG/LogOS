{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline where

import LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.Core as CoreImpl
import LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.ResourcePrinciple as ResourcePrincipleImpl
import LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.PowerLaw as PowerLawImpl
import LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.Experimental as ExperimentalImpl

-- Unified, LogOS-aligned pipeline (lightweight wrapper).
-- Core theorem path is controlled-feedback-native; transformer structure enters
-- only through bridge assumptions.
--
-- Lean/default surface:
-- - Core
-- - ResourcePrinciple
-- - PowerLaw
-- - Experimental
--
-- Full surface (explicit import, slower to check):
-- - LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.Full

module Core = CoreImpl
module ResourcePrinciple = ResourcePrincipleImpl
module PowerLaw = PowerLawImpl
module Experimental = ExperimentalImpl
