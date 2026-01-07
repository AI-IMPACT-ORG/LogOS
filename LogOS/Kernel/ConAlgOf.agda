{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.ConAlgOf where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Algebra.ConAlg
open import LogOS.Kernel

-- Extract the constraint algebra from a kernel.

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

