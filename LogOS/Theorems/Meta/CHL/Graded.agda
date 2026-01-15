{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.Graded where

-- Graded view: forget grading (at the step grade) to recover the CHL core.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)

open import LogOS.Kernel
open import LogOS.Kernel.Core as KCore
open import LogOS.Kernel.Graded
import LogOS.Kernel.Graded.ToKernel as ToKernel

import LogOS.Theorems.Meta.CHL.Core as Core

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : GradedKernel Sig Q)
  (stepSat : ToKernel.StepIsSat K)
  (bm : KCore.BodyMonotoneShape (GradedKernel.shape K))
  where

  K0 : Kernel Sig Q
  K0 = ToKernel.asKernel K stepSat bm

  module C = Core.For K0
  open C public
