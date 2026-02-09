{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.Core.Utils where

open import LogOS.Prelude

open import LogOS.Prelude.List using (List; []; _∷_)
open import LogOS.Prelude.Bool using (Bool; true; false)

-- Small utilities ------------------------------------------------------------

infix 4 _==ℕ_ _≤?ℕ_
infixl 6 _∸_
infix 0 if_then_else_

_==ℕ_ : ℕ → ℕ → Bool
zero  ==ℕ zero   = true
zero  ==ℕ suc _  = false
suc _ ==ℕ zero   = false
suc m ==ℕ suc n  = m ==ℕ n

_≤?ℕ_ : ℕ → ℕ → Bool
zero  ≤?ℕ _      = true
suc _ ≤?ℕ zero   = false
suc m ≤?ℕ suc n  = m ≤?ℕ n

if_then_else_ : ∀ {A : Set} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f

_∸_ : ℕ → ℕ → ℕ
zero  ∸ _      = zero
suc m ∸ zero   = suc m
suc m ∸ suc n  = m ∸ n

minus-zeroʳ : ∀ n → n ∸ 0 ≡ n
minus-zeroʳ zero    = refl
minus-zeroʳ (suc n) = refl

lookupDefault : ∀ {A : Set} → A → List A → ℕ → A
lookupDefault d []       _        = d
lookupDefault d (x ∷ xs) zero     = x
lookupDefault d (x ∷ xs) (suc i)  = lookupDefault d xs i

AllPred : ∀ {A : Set} → (A → Set) → List A → Set
AllPred _ []       = ⊤
AllPred P (x ∷ xs) = P x × AllPred P xs

lookupAllPred
  : ∀ {A : Set} (P : A → Set) (d : A) (xs : List A) (n : ℕ)
  → P d → AllPred P xs → P (lookupDefault d xs n)
lookupAllPred _ _ [] _ pd _ = pd
lookupAllPred _ _ (x ∷ _) zero _ (px , _) = px
lookupAllPred P d (_ ∷ xs) (suc n) pd (_ , pxs) =
  lookupAllPred P d xs n pd pxs

record BoundaryObs {ℓS ℓO : Level} (State : Set ℓS) : Set (lsuc (ℓS ⊔ ℓO)) where
  field
    Obs     : Set ℓO
    observe : State → Obs

EffectAt : ∀ {ℓS ℓO} {State : Set ℓS} → BoundaryObs {ℓS} {ℓO} State → Set (lsuc lzero ⊔ ℓO)
EffectAt B = BoundaryObs.Obs B → Set

infix 4 _⊨ᵇ_
_⊨ᵇ_ : ∀ {ℓS ℓO} {State : Set ℓS}
  → State → (B : BoundaryObs {ℓS} {ℓO} State) → EffectAt B → Set
_⊨ᵇ_ s B E = E (BoundaryObs.observe B s)
