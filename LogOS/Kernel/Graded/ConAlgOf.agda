{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.Graded.ConAlgOf where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.ConAlg
open import LogOS.Kernel.Graded

-- Extract the constraint algebra from a graded kernel.

conAlgOf
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → GradedKernel Sig Q → ConAlg {ℓ}
conAlgOf K = record
  { BB    = GradedKernel.BB K
  ; MBulk = GradedKernel.MBulk K
  ; MBnd  = GradedKernel.MBnd K
  ; Holo  = GradedKernel.Holo K
  }

