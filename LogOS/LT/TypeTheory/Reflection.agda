{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.TypeTheory.Reflection where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Reflection / guarded self-reference shell.
--
-- The actual constructions live in `LogOS.LT.Reflection` and
-- `LogOS.LT.Reflection.Laws`; this module only re-exports them under the
-- type-theory view.

import LogOS.LT.Flow as Flow
import LogOS.LT.Reflection as Reflection
import LogOS.LT.Reflection.Laws as Laws

open Flow public using (GuardedClosure; Flow; Stable; mkStable; elem; stable)
open Reflection public using (quot; evalm; evalm∘quot≈Flow; quot⊣evalm)
open Laws public using (ReflectionLawLike; reflectionLawLike; evalm∘quot-law; quot⊣evalm-law)
