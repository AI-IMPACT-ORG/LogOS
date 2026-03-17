{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Stacks where

-- Curated stack/program-layer surface for the logical-transformer core.
--
-- The default stack surface is refinement-first. Strict decode-coherence
-- utilities live under the explicit `LogOS.API.Strictification.Stack` import.

open import LogOS.LT.Stack public
