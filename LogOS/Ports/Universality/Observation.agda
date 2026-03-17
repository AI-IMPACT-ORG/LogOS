{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Universality.Observation where

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder)
open import LogOS.LT.View.Roles using (forget)
open import LogOS.LT.Kernel using (Kernel; bnd; Code; decodeView)
import LogOS.Ports.Opacity.Port as Opacity

-- Universality observation is just opacity with universality-facing names.
-- Read this as a vocabulary layer over `OpacityPort`, not as a second
-- one-view architecture.
ObservationPort
  : ∀ {ℓCode ℓBoundary ℓRelation : Level}
  → (CodeType : Set ℓCode)
  → (Boundary : ConPreorder ℓBoundary ℓRelation)
  → Set (lsuc (ℓCode ⊔ ℓBoundary ⊔ ℓRelation))
ObservationPort = Opacity.OpacityPort

observationView = Opacity.toView

kernelResultPort
  : ∀ {ℓKernel ℓRel ℓCode}
    (codeKernel : Kernel ℓKernel ℓRel ℓCode)
  → ObservationPort (Code codeKernel) (bnd codeKernel)
kernelResultPort codeKernel =
  Opacity.fromView (forget (decodeView codeKernel))
