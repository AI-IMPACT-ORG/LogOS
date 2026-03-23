{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Models.IterativeSetTree where

open import LogOS.Prelude hiding (zero)

open import LogOS.Prelude using (_⊎_; inj₁; inj₂)
open import LogOS.Prelude using (Σ; _,_)

-- Aczel-style iterative sets (W-style trees) as a pure syntax/presentation layer.
-- This is independent of any graph carrier and does not quotient by extensional equality.

data Botℓ {ℓ : Level} : Set ℓ where

data Natℓ {ℓ : Level} : Set ℓ where
  zero : Natℓ {ℓ}
  sucℓ : Natℓ {ℓ} → Natℓ {ℓ}

data V {ℓ : Level} : Set (lsuc ℓ) where
  sup : (I : Set ℓ) → (I → V {ℓ}) → V {ℓ}

-- Child index / child projection helpers for a tree node.

Idx : ∀ {ℓ} → V {ℓ} → Set ℓ
Idx (sup I _) = I

elemAt : ∀ {ℓ} (x : V {ℓ}) → Idx x → V {ℓ}
elemAt (sup _ f) = f

elemAt-subst
  : ∀ {ℓ} {x y : V {ℓ}}
  → (p : x ≡ y)
  → (i : Idx x)
  → elemAt y (subst Idx p i) ≡ elemAt x i
elemAt-subst refl _ = refl

-- Membership for V (definitional: elements are the children).

infix 4 _∈ᵛ_

_∈ᵛ_ : ∀ {ℓ} → V {ℓ} → V {ℓ} → Set (lsuc ℓ)
x ∈ᵛ sup I f = Σ I (λ i → x ≡ f i)

memberIn
  : ∀ {ℓ} {x z : V {ℓ}}
  → (i : Idx x)
  → z ≡ elemAt x i
  → z ∈ᵛ x
memberIn {x = sup _ _} i eq = i , eq

memberOut
  : ∀ {ℓ} {x z : V {ℓ}}
  → z ∈ᵛ x
  → Σ (Idx x) (λ i → z ≡ elemAt x i)
memberOut {x = sup _ _} (i , eq) = i , eq

-- Empty set and successor (von Neumann successor: a ↦ a ∪ {a}).

emptyᵛ : ∀ {ℓ} → V {ℓ}
emptyᵛ {ℓ} = sup (Botℓ {ℓ}) (λ ())

pairᵛ : ∀ {ℓ} → V {ℓ} → V {ℓ} → V {ℓ}
pairᵛ {ℓ} x y = sup (Topℓ {ℓ} ⊎ Topℓ {ℓ}) go
  where
    go : Topℓ {ℓ} ⊎ Topℓ {ℓ} → V {ℓ}
    go (inj₁ _) = x
    go (inj₂ _) = y

unionᵛ : ∀ {ℓ} → V {ℓ} → V {ℓ}
unionᵛ (sup I f) = sup (Σ I (λ i → Idx (f i))) (λ { (i , j) → elemAt (f i) j })

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
