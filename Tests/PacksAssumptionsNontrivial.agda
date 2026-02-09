{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.PacksAssumptionsNontrivial where

-- Stable assumption-bundle surface should remain typecheckable and not
-- accidentally force vacuous ports/adapters usage.

import LogOS.Packs.Assumptions.Surface
open import Tests.NontrivialPortsSpine public using (canonicalIdAdapterGuards₀)

