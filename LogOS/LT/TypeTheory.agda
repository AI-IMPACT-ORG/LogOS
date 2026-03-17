{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.TypeTheory where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Optional type-theory-flavoured view layer on the LT spine.
--
-- This module adds no axioms and does not change any refinement meaning: it is
-- a shallow naming/combinator toolkit that elaborates directly into existing
-- LT objects (kernels, homs, stacks, ports). Equality-based aliases live in
-- `LogOS.LT.TypeTheory.Strictification`.

import LogOS.LT.TypeTheory.Surface as Surface
import LogOS.LT.TypeTheory.Intensional as Intensional
import LogOS.LT.TypeTheory.Stack as Stack
import LogOS.LT.TypeTheory.Ports as Ports
import LogOS.LT.TypeTheory.Reflection as Reflection

open Surface public
open Intensional public
open Stack public
open Ports public
open Reflection public
