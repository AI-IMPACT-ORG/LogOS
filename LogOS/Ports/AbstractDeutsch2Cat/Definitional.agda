{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.AbstractDeutsch2Cat.Definitional where

open import LogOS.Prelude using (Level)
open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)

import LogOS.Ports.AbstractDeutsch2Cat as Deutsch2Cat

module Deutsch2CatLocal {ℓI ℓOCon ℓORel ℓCode : Level} (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}) where
  module Surface = Deutsch2Cat.Deutsch2CatLocal {ℓI} {ℓOCon} {ℓORel} {ℓCode} PS
  module Deutsch = Surface.Deutsch
