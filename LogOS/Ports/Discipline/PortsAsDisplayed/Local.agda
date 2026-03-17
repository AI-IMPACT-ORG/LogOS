{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Discipline.PortsAsDisplayed.Local where

open import LogOS.Prelude using (Level; _⊔_)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.LOG.Kernel2Cat using (LOG)
open import LogOS.Ports.PhysicalSemantics.Core using (DependentLocalSemantics)

import LogOS.Ports.AbstractDeutsch2Cat.Laws as DeutschLaws

-- Deutsch-style category discipline (parameterised by dependent shared-semantics data).
module PortsAsDisplayedLocal {ℓI ℓOCon ℓORel ℓCode : Level} (PS : DependentLocalSemantics {ℓI} {ℓOCon} {ℓORel}) where
  module DeutschLaws = DeutschLaws.Deutsch2CatLocal {ℓI} {ℓOCon} {ℓORel} {ℓCode} PS

  private
    forgetDeutschLOG-typed
      : Thin2Functor DeutschLaws.Deutsch.WithPort (LOG {ℓI ⊔ ℓOCon} {ℓI ⊔ ℓORel} {ℓCode})
    forgetDeutschLOG-typed = DeutschLaws.forgetDeutschLOG-typed
