{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.PacksUniversalIRNontrivial where

-- Stable UniversalIR surface should remain typecheckable and not regress the
-- non-triviality discipline used by the ports spine.

import LogOS.Packs.UniversalIR.Surface
open import Tests.NontrivialPortsSpine public using (canonicalIdAdapterGuards₀)

