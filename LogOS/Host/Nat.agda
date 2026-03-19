{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe --warning=noCoverageNoExactSplit #-}
module LogOS.Host.Nat where

-- Host wrapper around Agda.Builtin.Nat (ℕ).
--
-- This keeps the `ℕ` name across the codebase while avoiding duplicate BUILTIN bindings.

open import Agda.Builtin.Nat public renaming (Nat to ℕ)
