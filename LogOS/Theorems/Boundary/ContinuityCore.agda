{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Boundary.ContinuityCore where

-- Shared continuity/approximant wrappers for any guarded closure.

open import LogOS.Prelude
open import Data.Product using (_×_; _,_)
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth

module For {ℓ : Level}
  (CP : ConPoset ℓ)
  (GC : Truth.GuardedCore.GuardedClosure CP)
  where

  open ConPoset CP
  open Truth.GuardedCore

  Flow-continuity
    : (ωCPO : OmegaCPO CP)
      (FF   : FiniteFirst CP GC ωCPO)
      (f    : ℕ → Con)
    → (mono-chain : ∀ n → _⊑_ (f n) (f (suc n)))
    → _⊑_
        (GuardedClosure.Flow GC (OmegaCPO.supω ωCPO f))
        (OmegaCPO.supω ωCPO (λ n → GuardedClosure.Flow GC (f n)))
  Flow-continuity ωCPO FF f mono =
    FiniteFirst.cont-ω FF f mono

  Th*-as-sup
    : (ωCPO : OmegaCPO CP)
      (FF   : FiniteFirst CP GC ωCPO)
    → (_⊑_ (GuardedClosure.Th* GC) (OmegaCPO.supω ωCPO (FiniteFirst.approxS FF)))
      ×
      (_⊑_ (OmegaCPO.supω ωCPO (FiniteFirst.approxS FF)) (GuardedClosure.Th* GC))
  Th*-as-sup ωCPO FF =
    FiniteFirst.Th⋆-as-sup FF
