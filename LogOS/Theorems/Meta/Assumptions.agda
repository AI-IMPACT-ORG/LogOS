{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Assumptions where

-- Umbrella module re-exporting meta-theorem assumption packs.
--
-- Prefer importing the smallest relevant submodule:
-- - `LogOS.Theorems.Meta.ConditionalPacks` for structural packs (DecodeExtensional, provability ops)
-- - `LogOS.Theorems.Meta.Assumptions.Core` for non-diagonal axiom interfaces (e.g. `BoundaryFix`)
-- - `LogOS.Theorems.Meta.Assumptions.Diagonal` for diagonalisation/self-reference packs

open import LogOS.Theorems.Meta.ConditionalPacks public
open import LogOS.Theorems.Meta.Assumptions.Core public
open import LogOS.Theorems.Meta.Assumptions.Diagonal public
