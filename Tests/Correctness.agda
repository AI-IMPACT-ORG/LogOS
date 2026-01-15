{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.Correctness where

-- Explicit correctness surfaces should remain typecheckable.

import LogOS.Theorems.Meta.RefinementSoundness
import LogOS.Theorems.Meta.TruthLemma
import LogOS.Theorems.Meta.GuardedTruthAt
