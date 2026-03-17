{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.LOG.GuardedImplementationFlow2Cat where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

import LogOS.LT.LOG.ImplementationFlow2Cat.Core as Core

open Core public using
  ( ImplementationFlowStackUnder
  ; LOGᴳʳᶠ⊑
  ; LOGArchitectureImplementationFlowUnder
  )
