{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Tests.Kernel2CatGuards where

-- Smoke test: the existing kernel/logic-kernel/graded-kernel thin-2-category
-- packages remain typecheckable and expose their law bundles.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Thin2Cat using (Thin2CatLaws)

import LogOS.Kernel.Hom2Cat as K2
import LogOS.Kernel.Graded.Hom2Cat as GK2

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ} where

  lawsK : Thin2CatLaws (K2.KernelThin2Cat {ℓ = ℓ} {Sig = Sig} {Q = Q})
  lawsK = K2.KernelThin2CatLaws

  lawsGK : Thin2CatLaws (GK2.GradedKernelThin2Cat {ℓ = ℓ} {Sig = Sig} {Q = Q})
  lawsGK = GK2.GradedKernelThin2CatLaws
