{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.SemiDecider where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; _↔_; to; from)

open import LogOS.Prelude.Nat using (ℕ)
open import LogOS.Prelude.Product using (Σ; _,_; proj₁; proj₂)
open import LogOS.Prelude.Sum using (_⊎_)

-- A lightweight notion of semi-decidability:
-- a predicate P holds iff some bounded approximant Approx n holds, where each
-- approximant is itself decidable.
--
-- This matches common patterns in the library (bounded search → unbounded search),
-- without committing to a specific operational semantics.

record SemiDecider {ℓA ℓP ℓApprox : Level} (A : Set ℓA) (P : A → Set ℓP)
  : Set (lsuc (ℓA ⊔ ℓP ⊔ ℓApprox)) where
  field
    Approx     : ℕ → A → Set ℓApprox
    decApprox  : ∀ n x → Approx n x ⊎ ¬ Approx n x

    soundApprox : ∀ n x → Approx n x → P x
    complete    : ∀ x → P x → Σ ℕ (λ n → Approx n x)

  -- P is logically equivalent to existence of a bounded approximant.
  --
  -- (We keep this as a derived lemma rather than a field so call sites can
  --  use `Approx` directly without carrying extra proofs.)
  approx↔ : ∀ x → P x ↔ Σ ℕ (λ n → Approx n x)
  approx↔ x =
    record
      { to   = complete x
      ; from = λ ex → soundApprox (proj₁ ex) x (proj₂ ex)
      }

open SemiDecider public

-- Transport a semidecider across pointwise logical equivalence.
-- This keeps the bounded approximants unchanged.

mapSemiDecider
  : ∀ {ℓA ℓP ℓQ ℓApprox}
    {A : Set ℓA}
    {P : A → Set ℓP}
    {Q : A → Set ℓQ}
  → (∀ x → P x ↔ Q x)
  → SemiDecider {ℓApprox = ℓApprox} A P
  → SemiDecider {ℓApprox = ℓApprox} A Q
mapSemiDecider eq sd =
  record
    { Approx      = SemiDecider.Approx sd
    ; decApprox   = SemiDecider.decApprox sd
    ; soundApprox = λ n x ax → to (eq x) (SemiDecider.soundApprox sd n x ax)
    ; complete    = λ x qx → SemiDecider.complete sd x (from (eq x) qx)
    }
