{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.API.Assumptions.Core where

-- Shared “logic core” for domain assumption bundles:
-- a single `LogicKernel` instance (Curry–Howard–Lambek view), plus the derived
-- kernel *shape* (`KernelLike`) for components that only talk about code/decode.

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Kernel.LogicKernel using (LogicKernel)
open import LogOS.Kernel using (Kernel; KernelLike; kernelLike-fromLogicKernel)
open import LogOS.Kernel.Graded using (GradedKernel)
import LogOS.Kernel.LogicKernel.FromKernel as LKFromKernel
import LogOS.Kernel.LogicKernel.FromGradedKernel as LKFromGraded

record LogicCore {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
  field
    Sig : LogOSSignature ℓ
    Q   : QAdapter ℓ
    K   : LogicKernel Sig Q

  KLike : KernelLike Sig Q
  KLike = kernelLike-fromLogicKernel K

open LogicCore public

coreFromLogicKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → LogicKernel Sig Q
  → LogicCore {ℓ}
coreFromLogicKernel {Sig = Sig} {Q = Q} K =
  record { Sig = Sig ; Q = Q ; K = K }

coreFromKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → Kernel Sig Q
  → LogicCore {ℓ}
coreFromKernel {Sig = Sig} {Q = Q} K =
  record { Sig = Sig ; Q = Q ; K = LKFromKernel.asLogicKernel K }

coreFromGradedKernel
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → GradedKernel Sig Q
  → LogicCore {ℓ}
coreFromGradedKernel {Sig = Sig} {Q = Q} K =
  record { Sig = Sig ; Q = Q ; K = LKFromGraded.asLogicKernel K }
