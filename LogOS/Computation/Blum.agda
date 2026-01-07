{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.Blum where

open import LogOS.Prelude
open import LogOS.Computation.Core
open import LogOS.Syntax.Prop using (⊥; ¬_; _↔_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import LogOS.Computation.SemiDecider as SD

-- Blum-like structure (schematic). Models supply decidability and domain facts.

record Blum {ℓ : Level} (Code : Set ℓ) : Set (lsuc (lsuc ℓ)) where
  field
    Comp  : Computation Code
    TimeLe : ℕ → Code → Set ℓ                 -- time relation (e.g., Halts (iterate n code))
    Domain : Code → Set ℓ                     -- halting domain
    total  : ∀ c → Domain c → Σ ℕ (λ n → TimeLe n c)
    dec    : ∀ n c → TimeLe n c ⊎ ¬ (TimeLe n c)

-- Optional strengthening: if time witnesses always imply membership in the
-- chosen halting domain, then the domain is exactly the Join/colimit of the
-- bounded time predicates, and is semi-decidable.

record TimeLeSound {ℓ : Level} {Code : Set ℓ} (B : Blum Code) : Set (lsuc (lsuc ℓ)) where
  field
    sound : ∀ n c → Blum.TimeLe B n c → Blum.Domain B c

open TimeLeSound public

Domain↔ΣTimeLe
  : ∀ {ℓ} {Code : Set ℓ} (B : Blum Code)
  → TimeLeSound B
  → ∀ c → Blum.Domain B c ↔ Σ ℕ (λ n → Blum.TimeLe B n c)
Domain↔ΣTimeLe B S c =
  record
    { to   = Blum.total B c
    ; from = λ { (n , tn) → sound S n c tn }
    }

semiDomain
  : ∀ {ℓ} {Code : Set ℓ} (B : Blum Code)
  → TimeLeSound B
  → SD.SemiDecider Code (Blum.Domain B)
semiDomain B S =
  record
    { Approx      = Blum.TimeLe B
    ; decApprox   = Blum.dec B
    ; soundApprox = sound S
    ; complete    = Blum.total B
    }
