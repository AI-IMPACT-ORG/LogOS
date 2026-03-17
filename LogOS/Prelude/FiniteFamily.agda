{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Prelude.FiniteFamily where

-- Explicit finite presentations: an S-tier size and a bounded lookup map.

open import LogOS.Prelude
open import LogOS.Prelude.Fin using (Fin)

record FiniteFamily {ℓ : Level} (A : Set ℓ) : Set ℓ where
  field
    size : ℕ
    at   : Fin size → A

open FiniteFamily public

map
  : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}
  → (A → B)
  → FiniteFamily A
  → FiniteFamily B
map f xs =
  record
    { size = size xs
    ; at = λ i → f (at xs i)
    }
