{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.CHL.Guarded where

-- Guarded reading of the CHL core: `Box` as the stability (closure) operator.

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel

import LogOS.Theorems.Meta.CHL.Core as Core

module For
  {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  (K : Kernel Sig Q)
  where

  open Core.For K public
    renaming
      ( Box            to Guarded
      ; decode-Box     to decode-Guarded
      ; box-mono       to guarded-mono
      ; truth          to guarded-truth
      ; truth-fixed    to guarded-fixed
      ; truth-decoded  to guarded-truth-decoded
      )

  -- Guarded/stable fragment: mutual refinement with the guarded step.
  Stable : Ty → Set ℓ
  Stable γ = Refines γ (Guarded γ) × Refines (Guarded γ) γ

  stable-truth : Stable guarded-truth
  stable-truth = guarded-fixed
