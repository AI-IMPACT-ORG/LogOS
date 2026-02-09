{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.UngradedKernel.ConAlgOf where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.ConAlg
open import LogOS.Kernel.UngradedKernel

-- Extract the constraint algebra from an `UngradedKernel`.

conAlgOf
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → UngradedKernel Sig Q → ConAlg {ℓ}
conAlgOf K =
  record
    { BB    = UngradedKernel.BB K
    ; MBulk = UngradedKernel.MBulk K
    ; MBnd  = UngradedKernel.MBnd K
    ; Holo  = UngradedKernel.Holo K
    }
