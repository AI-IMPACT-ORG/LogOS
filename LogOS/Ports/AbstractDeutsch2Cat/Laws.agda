{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.AbstractDeutsch2Cat.Laws where

open import LogOS.Prelude using (Level; _⊔_)
open import LogOS.LT.Thin2Functor using (Thin2Functor; _∘F_)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)
open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)

import LogOS.Ports.AbstractDeutsch2Cat as Deutsch2Cat

module Deutsch2CatLocal {ℓI ℓOCon ℓORel ℓCode : Level} (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}) where
  module Surface = Deutsch2Cat.Deutsch2CatLocal {ℓI} {ℓOCon} {ℓORel} {ℓCode} PS
  module Locality = Surface.Locality
  module Causality = Surface.Causality
  module Deutsch = Surface.Deutsch

  forgetDeutschLOG-typed
    : Thin2Functor Deutsch.WithPort (LOG {ℓI ⊔ ℓOCon} {ℓI ⊔ ℓORel} {ℓCode})
  forgetDeutschLOG-typed = Locality.forgetPhysical ∘F (Causality.forget ∘F Deutsch.forget)
