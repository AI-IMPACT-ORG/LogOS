{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Kernel.Graded where

-- API wrapper: graded-kernel surface.
-- Downstream topic libraries should prefer this over importing `LogOS.Kernel.Graded` directly.

open import LogOS.Kernel.Graded public

