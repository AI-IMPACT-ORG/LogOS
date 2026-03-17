{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Valuation.QAdapter where

-- Valuation algebra / quantitative adapter.
--
-- This file provides `QAdapter` as an optional quantitative bus:
-- kernels remain refinement-first and decode-extensional, and numerics are
-- made explicit by equipping kernels with budget/time ports derived from a
-- chosen `QAdapter` (scale) and an explicit chosen `QClock Q` (time presentation)
-- (see `LogOS.Ports.Valuation.ScaleBoundary` and the budget ports).

open import LogOS.Prelude using (Level; lsuc)
open import LogOS.Prelude using (_≡_; refl; sym; ⊤; tt; ttℓ)

-- Quantitative adapter (scale) as a single parameter.
--
-- The scale is a (unital) prequantale in the finite-join sense: a preorder
-- with binary join/bottom and a monoid multiplication distributing over join.
-- This keeps instances constructive (no global supremum selector is assumed).
--
-- Time is intentionally *not* part of the base adapter:
-- talk about time/scale is always relative to a *chosen* clock/presentation
-- `QClock Q` (a time monoid + an embedding τ : Time → Scale satisfying laws).

record QAdapterCore (ℓ : Level) : Set (lsuc ℓ) where
  infix 4 _≤s_ _≤p_
  infixl 6 _⊔s_
  infixl 7 _·_
  field
    Scale   : Set ℓ
    _≤s_    : Scale → Scale → Set ℓ
    ≤s-refl : ∀ {a} → _≤s_ a a
    ≤s-trans : ∀ {a b c} → _≤s_ a b → _≤s_ b c → _≤s_ a c
    _⊔s_    : Scale → Scale → Scale
    ⊥s      : Scale
    ⊥s-least : ∀ a → _≤s_ ⊥s a
    ⊔s-ub₁  : ∀ a b → _≤s_ a (a ⊔s b)
    ⊔s-ub₂  : ∀ a b → _≤s_ b (a ⊔s b)
    ⊔s-least : ∀ {a b c} → _≤s_ a c → _≤s_ b c → _≤s_ (a ⊔s b) c
    _·_     : Scale → Scale → Scale
    e       : Scale
    ·-mono  : ∀ {a b c d} → _≤s_ a b → _≤s_ c d → _≤s_ (a · c) (b · d)
    _≤p_    : Scale → Scale → Set ℓ
    ≤p-refl : ∀ {a} → _≤p_ a a
    ≤p-trans : ∀ {a b c} → _≤p_ a b → _≤p_ b c → _≤p_ a c

record QAdapter (ℓ : Level) : Set (lsuc ℓ) where
  field
    core : QAdapterCore ℓ

  open QAdapterCore core public

  field
    -- S-tier presentation equalities (strict). Semantic laws live at `≈` in
    -- `LogOS.Ports.Valuation.AbstractJoinPrequantale`.
    ·-assoc
      : ∀ a b c
      → QAdapterCore._·_ core (QAdapterCore._·_ core a b) c
          ≡ QAdapterCore._·_ core a (QAdapterCore._·_ core b c)
    ·-idl
      : ∀ a
      → QAdapterCore._·_ core (QAdapterCore.e core) a ≡ a
    ·-idr
      : ∀ a
      → QAdapterCore._·_ core a (QAdapterCore.e core) ≡ a

    -- Distributivity over finite joins.
    ·-distl-⊔s
      : ∀ a b c
      → QAdapterCore._·_ core (QAdapterCore._⊔s_ core a b) c
          ≡ QAdapterCore._⊔s_ core
              (QAdapterCore._·_ core a c)
              (QAdapterCore._·_ core b c)
    ·-distr-⊔s
      : ∀ a b c
      → QAdapterCore._·_ core a (QAdapterCore._⊔s_ core b c)
          ≡ QAdapterCore._⊔s_ core
              (QAdapterCore._·_ core a b)
              (QAdapterCore._·_ core a c)

-- Chosen time presentation for a fixed scale adapter.
--
-- This is the discipline-enforcing move:
-- any statement involving “time” must name the clock choice explicitly.
record QClock {ℓ : Level} (Q : QAdapter ℓ) : Set (lsuc ℓ) where
  infixl 6 _+_
  field
    Time    : Set ℓ
    _+_     : Time → Time → Time
    zero    : Time
    τ       : Time → QAdapter.Scale Q

    +-assoc : ∀ t u v → ((t + u) + v) ≡ (t + (u + v))
    +-idl   : ∀ t → (zero + t) ≡ t
    +-idr   : ∀ t → (t + zero) ≡ t

    τ-+     : ∀ t u → τ (t + u) ≡ (QAdapter._·_ Q (τ t) (τ u))
    τ-zero  : τ zero ≡ QAdapter.e Q

-- Optional structure split (core operations vs strict equality laws).
-- This is additive: existing code can keep using `QAdapter` directly.

qAdapterCore : ∀ {ℓ} → QAdapter ℓ → QAdapterCore ℓ
qAdapterCore = QAdapter.core

-- Small builders -------------------------------------------------------------

-- Degenerate prequantale adapter (all structure is unique).
-- Useful for lightweight kernels and proof infrastructure where costs are irrelevant.

trivialQAdapter : ∀ {ℓ} → QAdapter ℓ
trivialQAdapter {ℓ} =
  record
    { core =
        record
          { Scale = ⊤ {ℓ}
          ; _≤s_ = λ _ _ → ⊤ {ℓ}
          ; ≤s-refl = tt
          ; ≤s-trans = λ _ _ → tt
          ; _⊔s_ = λ _ _ → tt
          ; ⊥s = tt
          ; ⊥s-least = λ _ → tt
          ; ⊔s-ub₁ = λ _ _ → tt
          ; ⊔s-ub₂ = λ _ _ → tt
          ; ⊔s-least = λ _ _ → tt
          ; _·_ = λ _ _ → tt
          ; e = tt
          ; ·-mono = λ _ _ → tt
          ; _≤p_ = λ _ _ → ⊤ {ℓ}
          ; ≤p-refl = tt
          ; ≤p-trans = λ _ _ → tt
          }
    ; ·-assoc = λ _ _ _ → refl
    ; ·-idl = λ { ttℓ → refl }
    ; ·-idr = λ { ttℓ → refl }
    ; ·-distl-⊔s = λ _ _ _ → refl
    ; ·-distr-⊔s = λ _ _ _ → refl
    }

-- Degenerate clock for any scale adapter: one time point, and τ is constantly `e`.
trivialQClock : ∀ {ℓ} (Q : QAdapter ℓ) → QClock Q
trivialQClock {ℓ} Q =
  record
    { Time = ⊤ {ℓ}
    ; _+_ = λ _ _ → tt
    ; zero = tt
    ; τ = λ _ → QAdapter.e Q
    ; +-assoc = λ _ _ _ → refl
    ; +-idl = λ { ttℓ → refl }
    ; +-idr = λ { ttℓ → refl }
    ; τ-+ = λ _ _ → sym (QAdapter.·-idl Q (QAdapter.e Q))
    ; τ-zero = refl
    }
