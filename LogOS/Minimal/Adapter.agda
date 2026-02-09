{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Minimal.Adapter where

open import LogOS.Prelude using (Level; lsuc)
open import LogOS.Prelude using (_≡_; refl; ⊤; tt; ttℓ)

-- Prequantale + Time adapter as a single parameter.
--
-- The Minimal core treats the scale as a (unital) prequantale in the *finite-join*
-- sense: a preorder with a binary join/bottom and a monoid multiplication that
-- distributes over join. This is enough for the library’s “budget algebra” and
-- keeps instances constructive (no global supremum selector is assumed).
--
-- For clarity: this is *not* ZFC’s Axiom of Choice; see the set-theory pack.
--
-- Law strength note:
-- `QAdapter` uses strict (`≡`) algebraic laws for join/product/time. When a
-- model only satisfies these laws up to refinement, use
-- `LogOS.Minimal.Prequantale.Prequantale` as the lax law layer.

record QAdapter (ℓ : Level) : Set (lsuc ℓ) where
  infix 4 _≤s_ _≤p_
  infixl 6 _+_
  infixl 6 _⊔s_
  infixl 7 _·_
  field
    -- Scale (prequantale-like carrier)
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

-- Optional structure split (core operations vs strict equality laws).
-- This is additive: existing code can keep using `QAdapter` directly.

record QAdapterCore (ℓ : Level) : Set (lsuc ℓ) where
  infix 4 _≤s_ _≤p_
  infixl 6 _+_
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
    Time    : Set ℓ
    _+_     : Time → Time → Time
    zero    : Time
    τ       : Time → Scale

record QAdapterEqLaws {ℓ : Level} (C : QAdapterCore ℓ) : Set (lsuc ℓ) where
  open QAdapterCore C
  field
    ·-assoc : ∀ a b c → ((a · b) · c) ≡ (a · (b · c))
    ·-idl   : ∀ a → (e · a) ≡ a
    ·-idr   : ∀ a → (a · e) ≡ a
    ·-distl-⊔s : ∀ a b c → ((a ⊔s b) · c) ≡ ((a · c) ⊔s (b · c))
    ·-distr-⊔s : ∀ a b c → (a · (b ⊔s c)) ≡ ((a · b) ⊔s (a · c))
    +-assoc : ∀ t u v → ((t + u) + v) ≡ (t + (u + v))
    +-idl   : ∀ t → (zero + t) ≡ t
    +-idr   : ∀ t → (t + zero) ≡ t
    τ-+     : ∀ t u → τ (t + u) ≡ (τ t · τ u)
    τ-zero  : τ zero ≡ e

qAdapterCore : ∀ {ℓ} → QAdapter ℓ → QAdapterCore ℓ
qAdapterCore Q =
  record
    { Scale = QAdapter.Scale Q
    ; _≤s_ = QAdapter._≤s_ Q
    ; ≤s-refl = QAdapter.≤s-refl Q
    ; ≤s-trans = QAdapter.≤s-trans Q
    ; _⊔s_ = QAdapter._⊔s_ Q
    ; ⊥s = QAdapter.⊥s Q
    ; ⊥s-least = QAdapter.⊥s-least Q
    ; ⊔s-ub₁ = QAdapter.⊔s-ub₁ Q
    ; ⊔s-ub₂ = QAdapter.⊔s-ub₂ Q
    ; ⊔s-least = QAdapter.⊔s-least Q
    ; _·_ = QAdapter._·_ Q
    ; e = QAdapter.e Q
    ; ·-mono = QAdapter.·-mono Q
    ; _≤p_ = QAdapter._≤p_ Q
    ; ≤p-refl = QAdapter.≤p-refl Q
    ; ≤p-trans = QAdapter.≤p-trans Q
    ; Time = QAdapter.Time Q
    ; _+_ = QAdapter._+_ Q
    ; zero = QAdapter.zero Q
    ; τ = QAdapter.τ Q
    }

qAdapterEqLaws : ∀ {ℓ} (Q : QAdapter ℓ) → QAdapterEqLaws (qAdapterCore Q)
qAdapterEqLaws Q =
  record
    { ·-assoc = QAdapter.·-assoc Q
    ; ·-idl = QAdapter.·-idl Q
    ; ·-idr = QAdapter.·-idr Q
    ; ·-distl-⊔s = QAdapter.·-distl-⊔s Q
    ; ·-distr-⊔s = QAdapter.·-distr-⊔s Q
    ; +-assoc = QAdapter.+-assoc Q
    ; +-idl = QAdapter.+-idl Q
    ; +-idr = QAdapter.+-idr Q
    ; τ-+ = QAdapter.τ-+ Q
    ; τ-zero = QAdapter.τ-zero Q
    }

mkQAdapter
  : ∀ {ℓ}
  → (C : QAdapterCore ℓ)
  → QAdapterEqLaws C
  → QAdapter ℓ
mkQAdapter C L =
  record
    { Scale = QAdapterCore.Scale C
    ; _≤s_ = QAdapterCore._≤s_ C
    ; ≤s-refl = QAdapterCore.≤s-refl C
    ; ≤s-trans = QAdapterCore.≤s-trans C
    ; _⊔s_ = QAdapterCore._⊔s_ C
    ; ⊥s = QAdapterCore.⊥s C
    ; ⊥s-least = QAdapterCore.⊥s-least C
    ; ⊔s-ub₁ = QAdapterCore.⊔s-ub₁ C
    ; ⊔s-ub₂ = QAdapterCore.⊔s-ub₂ C
    ; ⊔s-least = QAdapterCore.⊔s-least C
    ; _·_ = QAdapterCore._·_ C
    ; e = QAdapterCore.e C
    ; ·-assoc = QAdapterEqLaws.·-assoc L
    ; ·-idl = QAdapterEqLaws.·-idl L
    ; ·-idr = QAdapterEqLaws.·-idr L
    ; ·-mono = QAdapterCore.·-mono C
    ; ·-distl-⊔s = QAdapterEqLaws.·-distl-⊔s L
    ; ·-distr-⊔s = QAdapterEqLaws.·-distr-⊔s L
    ; _≤p_ = QAdapterCore._≤p_ C
    ; ≤p-refl = QAdapterCore.≤p-refl C
    ; ≤p-trans = QAdapterCore.≤p-trans C
    ; Time = QAdapterCore.Time C
    ; _+_ = QAdapterCore._+_ C
    ; zero = QAdapterCore.zero C
    ; τ = QAdapterCore.τ C
    ; +-assoc = QAdapterEqLaws.+-assoc L
    ; +-idl = QAdapterEqLaws.+-idl L
    ; +-idr = QAdapterEqLaws.+-idr L
    ; τ-+ = QAdapterEqLaws.τ-+ L
    ; τ-zero = QAdapterEqLaws.τ-zero L
    }

-- Small builders -------------------------------------------------------------

-- Trivial prequantale/time adapter (all structure is unique).
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
