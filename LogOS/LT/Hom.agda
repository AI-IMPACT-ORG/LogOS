{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Hom where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Stable façade over the pristine kernel-hom core.
--
-- Canonical internal imports should use `LogOS.LT.Hom.Core`.
open import LogOS.LT.Hom.Core public
import LogOS.LT.Hom.Laws as Laws

open Laws public
