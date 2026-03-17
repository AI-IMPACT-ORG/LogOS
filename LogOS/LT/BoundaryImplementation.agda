{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.BoundaryImplementation where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Stable façade over the pristine implementation core.
--
-- Canonical internal imports should use `LogOS.LT.BoundaryImplementation.Core`.

open import LogOS.LT.BoundaryImplementation.Core public
import LogOS.LT.BoundaryImplementation.Laws as Laws

open Laws public
