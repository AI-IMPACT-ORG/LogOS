{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Complexity.LanguageWitnessW where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Prelude using (ℕ; zero; suc)
open import LogOS.Prelude using (_⊎_)
open import LogOS.Prelude using (Σ; _,_; _×_; fst; snd)
open import LogOS.Prelude.NatOrder using (_≤ℕ_; z≤n; s≤s; ≤ℕ-refl) public

-- A more classical NP-style witness system:
-- witnesses live in a type `W x` whose *size* is bounded by a polynomial in `size x`,
-- rather than being an index in a bounded finite search space.

-- Input-indexed “language” and witness system.

record WitnessSystemW {ℓI ℓW ℓ : Level}
                      (Input : Set ℓI)
                      (P     : Input → Set ℓ)
                      : Set (lsuc (lsuc (ℓ ⊔ ℓI ⊔ ℓW))) where
  field
    W     : Input → Set ℓW
    wsize : ∀ {x} → W x → ℕ

    size  : Input → ℕ
    polyBound : ℕ → ℕ

    Check : ∀ x → W x → Set ℓ
    decCheck : ∀ x w → Check x w ⊎ ¬ Check x w

    sound : ∀ x w → Check x w → P x
    complete
      : ∀ x → P x →
        Σ (W x) (λ w → (wsize w ≤ℕ polyBound (size x)) × Check x w)
