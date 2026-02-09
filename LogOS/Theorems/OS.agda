{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.OS where

-- Curated entrypoint: OS-flavoured semantics theorems (noninterference,
-- refinement, safety/liveness, bisimulation up to boundary).

import LogOS.Theorems.OS.All as Allₜ

module All = Allₜ
