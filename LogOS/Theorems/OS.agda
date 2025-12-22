{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.OS where

-- Curated entrypoint: OS-flavoured semantics theorems (noninterference,
-- refinement, safety/liveness, bisimulation up to boundary).

import LogOS.Theorems.OS.All as Allₜ

module All = Allₜ
