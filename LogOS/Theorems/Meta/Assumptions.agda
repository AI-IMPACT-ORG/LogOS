{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Assumptions where

-- Umbrella module re-exporting meta-theorem assumption packs.
--
-- Prefer importing the smallest relevant submodule:
-- - `LogOS.Theorems.Meta.Assumptions.Core` for structural packs (DecodeExtensional, BoundaryFix, provability ops)
-- - `LogOS.Theorems.Meta.Assumptions.Diagonal` for diagonalisation/self-reference packs

open import LogOS.Theorems.Meta.Assumptions.Core public
open import LogOS.Theorems.Meta.Assumptions.Diagonal public
