{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.All where

-- Index module for the Complexity domain (discoverability only).

-- NOTE: This module is intentionally *lightweight*.
-- Import the concrete developments directly (or via the curated packs):
-- - `LogOS.Packs.Complexity.Experimental.*`
-- - `LogOS.Complexity.Targets.*`
-- - `LogOS.Complexity.Examples.*`
--
-- Namespaced index for targets: `LogOS.Complexity.Targets.All`.

import LogOS.Complexity.Targets.All as Targetsₜ

module Targets = Targetsₜ
