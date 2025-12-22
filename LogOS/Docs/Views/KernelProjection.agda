{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Docs.Views.KernelProjection where

-- Minimal “projection” helpers for documentation: re-export kernel fields
-- through stable names, so docs stay coupled to the actual kernel surface.

open import LogOS.Prelude
open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Kernel using (Kernel)
open import LogOS.Minimal.Truth as Truth

module For {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ) (K : Kernel Sig Q) where
  open Kernel K public

  module TruthGT = Truth.GuardedTruth Sig Q
  open TruthGT using (GuardedClosure)

  open GuardedClosure (Kernel.GTruth K) public
    renaming
      ( Flow to Flow
      ; Th* to Th*
      )
