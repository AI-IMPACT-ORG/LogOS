{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.TypeTheory.Stack where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Stack-level re-exports.
--
-- The canonical implementations live in `LogOS.LT.Stack.Builders`; the
-- type-theory shell only records those deep constructions.

import LogOS.LT.Stack as Stack

open Stack public using
  ( StackDecodeLaw
  ; mkStackMapLike
  ; mkStackMap
  ; mkStackMap⊑
  ; mkStackKernelHomLike
  ; mkStackKernelHom
  ; mkStackKernelHom⊑
  ; mapCodeFrom
  )
