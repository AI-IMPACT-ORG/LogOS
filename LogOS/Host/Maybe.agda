{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Host.Maybe where

-- Bridge to Agda built-in maybes to avoid duplicate BUILTIN bindings.

open import Agda.Builtin.Maybe public

