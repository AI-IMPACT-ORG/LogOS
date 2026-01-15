{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Adapter where

open import Host.Level using (Level; lsuc)
open import LogOS.Prelude using (_≡_; refl; ⊤; tt; ttℓ)

-- Quantale + Time adapter as a single parameter.
--
-- The Minimal core treats the scale as a (unital) quantale in the *finite-join*
-- sense: a preorder with a binary join/bottom and a monoid multiplication that
-- distributes over join. This is enough for the library’s “budget algebra” and
-- keeps instances constructive (no global supremum selector is assumed).
--
-- For clarity: this is *not* ZFC’s Axiom of Choice; see the set-theory pack.

record QAdapter (ℓ : Level) : Set (lsuc ℓ) where
  infix 4 _≤s_ _≤p_
  infixl 6 _+_
  infixl 6 _⊔s_
  infixl 7 _·_
  field
    -- Scale (quantale-like carrier)
    Scale   : Set ℓ
    _≤s_    : Scale → Scale → Set ℓ
    ≤s-refl : ∀ {a} → _≤s_ a a
    ≤s-trans : ∀ {a b c} → _≤s_ a b → _≤s_ b c → _≤s_ a c

    -- Finite joins (binary sup) + bottom
    _⊔s_    : Scale → Scale → Scale
    ⊥s      : Scale
    ⊥s-least : ∀ a → _≤s_ ⊥s a
    ⊔s-ub₁  : ∀ a b → _≤s_ a (a ⊔s b)
    ⊔s-ub₂  : ∀ a b → _≤s_ b (a ⊔s b)
    ⊔s-least : ∀ {a b c} → _≤s_ a c → _≤s_ b c → _≤s_ (a ⊔s b) c

    _·_     : Scale → Scale → Scale
    e       : Scale
    ·-assoc : ∀ a b c → ((a · b) · c) ≡ (a · (b · c))
    ·-idl   : ∀ a → (e · a) ≡ a
    ·-idr   : ∀ a → (a · e) ≡ a

    -- Multiplication is monotone w.r.t. the scale preorder.
    ·-mono  : ∀ {a b c d} → _≤s_ a b → _≤s_ c d → _≤s_ (a · c) (b · d)

    -- Distributivity over finite joins
    ·-distl-⊔s : ∀ a b c → ((a ⊔s b) · c) ≡ ((a · c) ⊔s (b · c))
    ·-distr-⊔s : ∀ a b c → (a · (b ⊔s c)) ≡ ((a · b) ⊔s (a · c))

    -- Optional proof/derivability order (can coincide with _≤s_)
    _≤p_    : Scale → Scale → Set ℓ
    ≤p-refl : ∀ {a} → _≤p_ a a
    ≤p-trans : ∀ {a b c} → _≤p_ a b → _≤p_ b c → _≤p_ a c

    -- Time monoid and a homomorphism into Scale
    Time    : Set ℓ
    _+_     : Time → Time → Time
    zero    : Time
    τ       : Time → Scale
    +-assoc : ∀ t u v → ((t + u) + v) ≡ (t + (u + v))
    +-idl   : ∀ t → (zero + t) ≡ t
    +-idr   : ∀ t → (t + zero) ≡ t
    τ-+     : ∀ t u → τ (t + u) ≡ (τ t · τ u)
    τ-zero  : τ zero ≡ e

-- Small builders -------------------------------------------------------------

-- Trivial quantale/time adapter (all structure is unique).
-- Useful for lightweight kernels and proof infrastructure where costs are irrelevant.

trivialQAdapter : ∀ {ℓ} → QAdapter ℓ
trivialQAdapter {ℓ} =
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
    ; ·-assoc = λ _ _ _ → refl
    ; ·-idl = λ { ttℓ → refl }
    ; ·-idr = λ { ttℓ → refl }
    ; ·-mono = λ _ _ → tt
    ; ·-distl-⊔s = λ _ _ _ → refl
    ; ·-distr-⊔s = λ _ _ _ → refl
    ; _≤p_ = λ _ _ → ⊤ {ℓ}
    ; ≤p-refl = tt
    ; ≤p-trans = λ _ _ → tt
    ; Time = ⊤ {ℓ}
    ; _+_ = λ _ _ → tt
    ; zero = tt
    ; τ = λ _ → tt
    ; +-assoc = λ _ _ _ → refl
    ; +-idl = λ { ttℓ → refl }
    ; +-idr = λ { ttℓ → refl }
    ; τ-+ = λ _ _ → refl
    ; τ-zero = refl
    }
