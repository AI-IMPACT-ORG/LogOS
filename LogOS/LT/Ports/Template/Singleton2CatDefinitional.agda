{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Ports.Template.Singleton2CatDefinitional where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

open import LogOS.Prelude

import LogOS.LT.Ports.Template.Singleton2Cat as Template

open Template.Singleton2Cat public using
  ( displayed≡
  ; withPort≡
  ; forget≡
  )
