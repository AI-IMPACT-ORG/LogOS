{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Comparisons.Limitations where

open import LogOS.Prelude

-- “Limitations” for agents are instances of the existing opacity/diagonal
-- machinery: total, budget-bounded auditors do not exist under the usual
-- diagonal representability assumptions.

open import LogOS.Packs.Agents.Safety.NoTotalAuditor public

