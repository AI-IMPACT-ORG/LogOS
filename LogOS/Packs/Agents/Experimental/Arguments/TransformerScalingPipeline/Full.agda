{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Experimental.Arguments.TransformerScalingPipeline.Full where

-- Full pipeline anchor module.
--
-- The heavy pipeline components are checked directly in the CI/check-all path:
-- - TransformerScalingPipeline.Calibration
-- - TransformerScalingPipeline.ExperimentalCompute
-- - TransformerScalingPipeline.Examples
--
-- This module intentionally remains lightweight to avoid duplicate elaboration
-- cost from re-aliasing large experimental modules.
