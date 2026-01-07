{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.FromKernel where

open import LogOS.Prelude

open import LogOS.Kernel
open import LogOS.Kernel.Graded
open import LogOS.Computation.Core
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter

-- Derive a Computation instance from a Kernel: Code = Kernel.Code,
-- Step = Guard ∘ Body (the canonical code-level Flow), and
-- Halts = (γ ≡ Guard (Body γ)).

module FromKernel {ℓ : Level}
                  (Sig : LogOSSignature ℓ)
                  (Q   : QAdapter ℓ)
                  (K   : Kernel Sig Q) where
  open Kernel K
  Comp : Computation Code
  Comp = record
    { Step  = λ γ → Guard (Body γ)
    ; Halts = λ γ → γ ≡ Guard (Body γ)
    }

-- Derive a Computation instance from a GradedKernel in the same way:
-- Step = Guard ∘ Body (the canonical code-level Flow), and
-- Halts = (γ ≡ Guard (Body γ)).

module FromGradedKernel {ℓ : Level}
                        (Sig : LogOSSignature ℓ)
                        (Q   : QAdapter ℓ)
                        (K   : GradedKernel Sig Q) where
  open GradedKernel K
  Comp : Computation Code
  Comp = record
    { Step  = λ γ → Guard (Body γ)
    ; Halts = λ γ → γ ≡ Guard (Body γ)
    }
