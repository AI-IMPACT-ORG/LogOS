{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Data.Nat where

-- Bridge to Agda built-in naturals to avoid duplicate BUILTIN bindings
-- while keeping the ℕ name across the codebase.

open import Agda.Builtin.Nat public renaming (Nat to ℕ)
