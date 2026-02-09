{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Assumptions.Core where

-- Shared “logic core” for domain assumption bundles:
-- a single `Kernel` instance (Curry–Howard–Lambek view), plus the derived
-- kernel *shape* (`KernelLike`) for components that only talk about code/decode.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter

open import LogOS.Kernel using (Kernel; KernelLike; kernelLike-fromKernel)
import LogOS.Kernel.UngradedKernel as UK
import LogOS.Kernel.Graded as GK
import LogOS.Kernel.FromUngradedKernel as FromU
import LogOS.Kernel.FromGradedKernel as FromG

record LogicCore {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
  field
    Sig : LogOSSignature ℓ
    Q   : QAdapter ℓ
    K   : Kernel Sig Q

  KLike : KernelLike Sig Q
  KLike = kernelLike-fromKernel K

open LogicCore public

coreFromKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → Kernel Sig Q
  → LogicCore {ℓ}
coreFromKernel {Sig = Sig} {Q = Q} K =
  record { Sig = Sig ; Q = Q ; K = K }

coreFromUngradedKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → UK.UngradedKernel Sig Q
  → LogicCore {ℓ}
coreFromUngradedKernel {Sig = Sig} {Q = Q} K =
  record { Sig = Sig ; Q = Q ; K = FromU.asKernel K }

coreFromGradedKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → GK.GradedKernel Sig Q
  → LogicCore {ℓ}
coreFromGradedKernel {Sig = Sig} {Q = Q} K =
  record { Sig = Sig ; Q = Q ; K = FromG.asKernel K }
