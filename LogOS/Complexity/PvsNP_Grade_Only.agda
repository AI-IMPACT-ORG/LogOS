{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.PvsNP_Grade_Only where

open import LogOS.Prelude

import LogOS.Complexity.TruthRoute_Grade_Only as TruthRoute_Grade_Only

-- Stable, downstream-friendly entrypoint:
-- open `LogOS.Complexity.PvsNP_Grade_Only.For` for the uniform grade-only route.
-- This is a total (P/NP-shaped) interface, not classical language-relative NP.
module For = TruthRoute_Grade_Only.Uniform
