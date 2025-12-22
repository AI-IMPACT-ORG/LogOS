{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Data.Bool where

-- Bridge to Agda built-in booleans to avoid duplicate BUILTIN bindings
-- while keeping the `Bool`/`true`/`false` names consistent across the library.

open import Agda.Builtin.Bool public

