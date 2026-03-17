{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.Bridge.ObservationPrograms.ParOnKernels where

open import LogOS.Prelude
open import LogOS.LT.Kernel using (Kernel; CodePreorder)
open import LogOS.LT.Thin2Cat using (Thin2Cat; PullbackThin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor; forgetPullbackThin2Functor)

import LogOS.Apps.TuringCategory.PartialMaps as PM

-- --------------------------------------------------------------------------
-- Reindex Par to kernels via `CodePreorder`.

ParOnKernels
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Cat
      (lsuc (ℓ ⊔ ℓRel ⊔ ℓCode))
      (ℓCode ⊔ ℓRel)
      (ℓCode ⊔ ℓRel)
ParOnKernels {ℓ} {ℓRel} {ℓCode} =
  PullbackThin2Cat
    {C = PM.Par {ℓCon = ℓCode} {ℓRel = ℓRel}}
    (Kernel ℓ ℓRel ℓCode)
    CodePreorder

-- Forgetful functor `ParOnKernels → Par` (identity on morphisms).
forgetParOnKernels
  : ∀ {ℓ ℓRel ℓCode : Level}
  → Thin2Functor
      (ParOnKernels {ℓ} {ℓRel} {ℓCode})
      (PM.Par {ℓCon = ℓCode} {ℓRel = ℓRel})
forgetParOnKernels {ℓ} {ℓRel} {ℓCode} =
  forgetPullbackThin2Functor (Kernel ℓ ℓRel ℓCode) CodePreorder
