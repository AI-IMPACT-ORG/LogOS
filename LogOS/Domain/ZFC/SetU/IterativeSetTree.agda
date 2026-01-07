{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.ZFC.SetU.IterativeSetTree where

open import LogOS.Prelude

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_)

-- Aczel-style iterative sets (W-style trees) as a pure syntax/presentation layer.
-- This is independent of any graph carrier.

data Botℓ {ℓ : Level} : Set ℓ where

data Natℓ {ℓ : Level} : Set ℓ where
  zero : Natℓ {ℓ}
  sucℓ : Natℓ {ℓ} → Natℓ {ℓ}

data V {ℓ : Level} : Set (lsuc ℓ) where
  sup : (I : Set ℓ) → (I → V {ℓ}) → V {ℓ}

-- Membership for V (definitional: elements are the children).

infix 4 _∈ᵛ_

_∈ᵛ_ : ∀ {ℓ} → V {ℓ} → V {ℓ} → Set (lsuc ℓ)
x ∈ᵛ sup I f = Σ I (λ i → x ≡ f i)

-- Empty set and successor (von Neumann successor: a ↦ a ∪ {a}).

emptyᵛ : ∀ {ℓ} → V {ℓ}
emptyᵛ {ℓ} = sup (Botℓ {ℓ}) (λ ())

succᵛ : ∀ {ℓ} → V {ℓ} → V {ℓ}
succᵛ {ℓ} (sup I f) = sup (Topℓ {ℓ} ⊎ I) go
  where
    go : (Topℓ {ℓ} ⊎ I) → V
    go (inj₁ ttℓ) = sup I f
    go (inj₂ i)  = f i

-- von Neumann naturals and ω as a single V object.

vnNatᵛ : ∀ {ℓ} → Natℓ {ℓ} → V {ℓ}
vnNatᵛ zero = emptyᵛ
vnNatᵛ (sucℓ n) = succᵛ (vnNatᵛ n)

omegaᵛ : ∀ {ℓ} → V {ℓ}
omegaᵛ {ℓ} = sup (Natℓ {ℓ}) (vnNatᵛ {ℓ})
