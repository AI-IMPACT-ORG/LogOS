{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.Interpretation where

-- Transformer-aligned Set.MM interpretation helpers.
--
-- This module is deliberately “pipeline-shaped”; see:
-- - `Interpretation.Close`     : close Metamath's implicit outer ∀ over set variables
-- - `Interpretation.Pipeline`  : parsing pipeline records + bulk parser
-- - `Interpretation.Normalize` : normalisation (drop vacuous quantifiers)
-- - `Interpretation.Interpret` : meta-free interpretation step
-- - `Interpretation.DB`        : convenience layer for DB ports + ZF ledger bundles

import LogOS.Apps.ZFC.Metamath.Interpretation.Close as Close
import LogOS.Apps.ZFC.Metamath.Interpretation.Pipeline as Pipeline
import LogOS.Apps.ZFC.Metamath.Interpretation.Normalize as Normalize
import LogOS.Apps.ZFC.Metamath.Interpretation.Interpret as Interpret
import LogOS.Apps.ZFC.Metamath.Interpretation.DB as DB

open Close public
open Pipeline public
open Normalize public
open Interpret public
open DB public
