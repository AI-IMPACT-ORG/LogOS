{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.Surface where

-- Stable adapter surface: view/adaptation maps for signatures, kernels, and ports.
--
-- Tool-facing I/O and computation/process morphisms live under `LogOS.API.Architecture`
-- (see `Architecture.Tooling` / `Architecture.Computation`).

open import LogOS.Adapters.Core public

