{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.ZFC.Surface where

-- Surface lock for the ZF/ZFC storyline:
-- re-export the pack entrypoints plus the paper-facing code/formula interfaces.

open import LogOS.Packs.ZFC.All public

-- Keep this surface namespaced via `All` to avoid clashes with other packs and
-- to keep the ZFC public entrypoint stable.
