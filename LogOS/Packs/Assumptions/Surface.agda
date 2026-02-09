{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Assumptions.Surface where

-- Surface lock for the stable assumption-bundle umbrella:
-- keeps the entrypoint stable while allowing the internal module structure
-- to evolve.

open import LogOS.Packs.Assumptions.All public

