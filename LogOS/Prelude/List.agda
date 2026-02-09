{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Prelude.List where

open import LogOS.Host.List public

open import LogOS.Prelude using (Level; _⊔_)
open import LogOS.Prelude using (Σ; _,_)

-- Minimal list-wise predicate (avoid pulling in an external stdlib).
data All {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁}
         (P : A → Set ℓ₂) : List A → Set (ℓ₁ ⊔ ℓ₂) where
  all[] : All P []
  all∷  : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

All-map
  : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁}
    {P : A → Set ℓ₂} {Q : A → Set ℓ₃}
  → (∀ x → P x → Q x)
  → ∀ {xs} → All P xs → All Q xs
All-map f all[] = all[]
All-map f (all∷ px pxs) = all∷ (f _ px) (All-map f pxs)

All-++
  : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
  → ∀ {xs ys} → All P xs → All P ys → All P (xs ++ ys)
All-++ all[] ys = ys
All-++ (all∷ px pxs) ys = all∷ px (All-++ pxs ys)

All-concat
  : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
  → ∀ {xss} → All (All P) xss → All P (concat xss)
All-concat all[] = all[]
All-concat (all∷ px pxs) = All-++ px (All-concat pxs)

-- Extract the list-of-lists payload from an All of dependent pairs.
listsOf
  : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁}
    {R : A → List A → Set ℓ₂}
    {cs : List A}
  → All (λ c → Σ (List A) (λ ds → R c ds)) cs
  → List (List A)
listsOf all[] = []
listsOf (all∷ (ds , _) rest) = ds ∷ listsOf rest
