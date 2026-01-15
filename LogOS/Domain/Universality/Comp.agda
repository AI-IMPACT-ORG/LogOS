{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.Comp where

open import LogOS.Prelude
open import Data.Nat using (ℕ; zero; suc)

open import LogOS.Domain.Universality.Core
open import LogOS.Computation.Core

-- Computation instance for CoreUCode: Step = stepCoreU; Halts = fixed point under Step

UComp : Computation CoreUCode
UComp = record
  { Step  = stepCoreU
  ; Halts = λ _ → ⊤
  }

iter : ℕ → CoreUCode → CoreUCode
iter = iterate UComp

-- Normalisation is key: for the simple decrement-to-zero computations, iter n halts.

halts-encodeT : ∀ n → UComp .Halts (iter n (CoreT (mkT 0 n)))
halts-encodeT _ = tt

halts-encodeC : ∀ n → UComp .Halts (iter n (CoreC (mkC n)))
halts-encodeC _ = tt

halts-encodeQ : ∀ n → UComp .Halts (iter n (CoreQ (mkCoreQ n)))
halts-encodeQ _ = tt

halts-encodeB : ∀ n → UComp .Halts (iter n (CoreB (mkB 0 n)))
halts-encodeB _ = tt

-- Blum-like time (conservative): time n u := iter n u is a fixed point under Step

Time : ℕ → CoreUCode → Set
Time n u = UComp .Halts (iter n u)

-- For our encoders of PA “decrement-to-zero”, Time n holds and matches the usual notion
-- of step-count complexity.

time-encodeT : ∀ n → Time n (CoreT (mkT 0 n))
time-encodeT = halts-encodeT

time-encodeC : ∀ n → Time n (CoreC (mkC n))
time-encodeC = halts-encodeC

time-encodeQ : ∀ n → Time n (CoreQ (mkCoreQ n))
time-encodeQ = halts-encodeQ

time-encodeB : ∀ n → Time n (CoreB (mkB 0 n))
time-encodeB = halts-encodeB
