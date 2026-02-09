{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.ConAlgOf where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.ConAlg
open import LogOS.Kernel

-- Extract the constraint algebra from a `Kernel`.

conAlgOf
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → Kernel Sig Q → ConAlg {ℓ}
conAlgOf K =
  record
    { BB    = Kernel.BB K
    ; MBulk = Kernel.MBulk K
    ; MBnd  = Kernel.MBnd K
    ; Holo  = Kernel.Holo K
    }

