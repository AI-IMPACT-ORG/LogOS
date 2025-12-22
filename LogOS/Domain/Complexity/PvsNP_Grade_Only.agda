{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.PvsNP_Grade_Only where

open import LogOS.Prelude

import LogOS.Domain.Complexity.TruthRoute_Grade_Only as TruthRoute_Grade_Only

-- Stable, downstream-friendly entrypoint:
-- open `LogOS.Domain.Complexity.PvsNP_Grade_Only.For` for the grade-only route.
module For = TruthRoute_Grade_Only.For
