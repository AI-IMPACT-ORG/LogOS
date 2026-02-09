{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.PacksInfoTheoryNontrivial where

-- Stable InfoTheory surface should stay typecheckable; this also keeps the
-- ports/adapters non-triviality witnesses in the CI closure.

import LogOS.Packs.InfoTheory.Surface
open import Tests.NontrivialPortsSpine public using (canonicalIdAdapterGuards₀)

