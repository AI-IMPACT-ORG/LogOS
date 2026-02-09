{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.UniversalIR.Surface where

-- Surface lock for the UniversalIR pack.

open import LogOS.Packs.UniversalIR.All public
-- Keep this as a *namespaced* surface to avoid collisions between the internal
-- module structure of `UniversalIR.Core` and the curated `All` pack surface.
