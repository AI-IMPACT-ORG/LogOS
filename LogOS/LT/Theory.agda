{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Theory where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Theories as first-class objects + provability as transformer.
--
-- The real content lives in the submodules:
-- - `LogOS.LT.Theory.Rules`: general finitary rule closure (Metamath-style).
-- - `LogOS.LT.Theory.HilbertMP`: minimal Hilbert system as a special case.

import LogOS.LT.Theory.Rules
import LogOS.LT.Theory.HilbertMP

module Rules = LogOS.LT.Theory.Rules
module HilbertMP = LogOS.LT.Theory.HilbertMP.HilbertMPLocal
