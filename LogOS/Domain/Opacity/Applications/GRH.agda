{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Opacity.Applications.GRH where

-- GRH as an application of the Opacity strand.
--
-- This is a namespaced index surface. For curated entrypoints, prefer the pack
-- surface `LogOS.Packs.Opacity.Experimental.Applications.GRH`.
--
-- The Opacity strand itself (ledgers, observability, opacity/barrier theorems)
-- lives under `LogOS.Domain.Opacity.*`.

open import LogOS.Domain.Opacity.Applications.GRH.All public
