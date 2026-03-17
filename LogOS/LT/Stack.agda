{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Stack where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Curated stack surface.
--
-- - core stack-as-kernel construction: `LogOS.LT.Stack.Core`
-- - explicit strictification utilities: `LogOS.LT.Stack.Strictification`
-- - optional macro/program layer: `LogOS.LT.Stack.Program`
--
-- Importing `LogOS.LT.Stack` gives the canonical refinement-first stack surface
-- (Core + Program). Strictification stays behind an explicit import.
--
-- Policy note:
-- we avoid `open import ... public` here (reserved for API/Prelude) and instead
-- re-export by `import` + `open ... public`.

import LogOS.LT.Stack.Core as Core
import LogOS.LT.Stack.Builders as Builders
import LogOS.LT.Stack.Extend as Extend
import LogOS.LT.Stack.Laws as Laws
import LogOS.LT.Stack.Program as Program

open Core public
open Builders public
open Extend public
open Laws public
open Program public
