{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Data.Bool where

-- Bridge to Agda built-in booleans to avoid duplicate BUILTIN bindings
-- while keeping the `Bool`/`true`/`false` names consistent across the library.

open import Agda.Builtin.Bool public

