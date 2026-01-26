{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.ConAlgOf where

open import LogOS.Prelude

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Algebra.ConAlg
open import LogOS.Kernel.LogicKernel

-- Extract the constraint algebra from a `LogicKernel`.

conAlgOf
  : ∀ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  → LogicKernel Sig Q → ConAlg {ℓ}
conAlgOf K =
  record
    { BB    = LogicKernel.BB K
    ; MBulk = LogicKernel.MBulk K
    ; MBnd  = LogicKernel.MBnd K
    ; Holo  = LogicKernel.Holo K
    }

