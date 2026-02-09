{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.PacksAgentsNontrivial where

-- Stable pack surface should remain typecheckable and compatible with the
-- non-triviality witnesses used by the ports/adapters spine.

import LogOS.Packs.Agents.Surface
open import Tests.NontrivialPortsSpine public using (canonicalIdAdapterGuards₀)

