{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.All where

-- Power-user umbrella: re-export the major theorem surfaces.
--
-- Prefer `LogOS.Theorems.Surface` unless you explicitly want the larger namespace.

open import LogOS.Theorems.Surface public

import LogOS.Theorems.CategoryTheory.All as CategoryTheoryₜ
import LogOS.Theorems.Modal.All as Modalₜ
import LogOS.Theorems.Reflection.All as Reflectionₜ

module CategoryTheory = CategoryTheoryₜ
module Modal = Modalₜ
module Reflection = Reflectionₜ
