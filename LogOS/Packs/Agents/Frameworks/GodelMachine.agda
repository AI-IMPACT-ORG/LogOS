{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Frameworks.GodelMachine where

open import LogOS.Prelude

-- Gödel-machine-style metareasoning is already present as assumption-based
-- meta-theory. This module is intentionally lightweight and simply re-exports
-- the relevant theorem surface.

open import LogOS.Theorems.Meta.Godel public

