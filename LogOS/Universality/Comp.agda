{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Universality.Comp where

open import LogOS.Prelude
open import LogOS.Prelude using (ℕ; zero; suc)

open import LogOS.Universality.Core
open import LogOS.Universality.Kernel as UK
open import LogOS.Computation.Core

-- Computation instance for CoreUCode: Step = stepCoreU; Halts = fixed point under Step

UComp : Computation CoreUCode
UComp = UK.UKComp

iter : ℕ → CoreUCode → CoreUCode
iter = UK.iterateUK

-- Normalisation is key: for the decrement-to-zero encoders on Church/chain branches,
-- iter n reaches a fixed point under Step.

halts-encodeC : ∀ n → UComp .Halts (iter n (CoreC (mkC n)))
halts-encodeC zero    = refl
halts-encodeC (suc n) = halts-encodeC n

halts-encodeB′ : ∀ pc n → UComp .Halts (iter n (CoreB (mkB pc n)))
halts-encodeB′ pc zero    = refl
halts-encodeB′ pc (suc n) = halts-encodeB′ (suc pc) n

halts-encodeB : ∀ n → UComp .Halts (iter n (CoreB (mkB 0 n)))
halts-encodeB n = halts-encodeB′ 0 n

-- Blum-like time (conservative): time n u := iter n u is a fixed point under Step

Time : ℕ → CoreUCode → Set
Time n u = UComp .Halts (iter n u)

-- For our encoders of PA “decrement-to-zero”, Time n holds and matches the usual notion
-- of step-count complexity.

time-encodeC : ∀ n → Time n (CoreC (mkC n))
time-encodeC = halts-encodeC

time-encodeB : ∀ n → Time n (CoreB (mkB 0 n))
time-encodeB = halts-encodeB
