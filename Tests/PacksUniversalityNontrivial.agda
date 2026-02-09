{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.PacksUniversalityNontrivial where

-- Stable Universality surface should remain typecheckable and compatible with
-- the non-triviality witnesses for boundary satisfaction.

import LogOS.Packs.Universality.Surface
open import Tests.NontrivialPortsSpine public using (canonicalIdAdapterGuards₀)

