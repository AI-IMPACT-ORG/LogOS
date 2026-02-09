{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Adapters.All where

-- Power-user adapter umbrella (transport/translation + tooling).
--
-- Prefer `LogOS.Adapters.Surface` unless you explicitly want the larger namespace.

open import LogOS.Adapters.Views.All public
