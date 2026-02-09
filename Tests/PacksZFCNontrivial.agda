{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.PacksZFCNontrivial where

-- Stable ZFC surface should stay typecheckable; keep it in CI alongside the
-- ports/adapters non-triviality witness closure.

import LogOS.Packs.ZFC.Surface
open import Tests.NontrivialPortsSpine public using (canonicalIdAdapterGuards₀)

