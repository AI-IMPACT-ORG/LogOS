{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.Core.Lambda where

open import LogOS.Prelude
open import LogOS.UniversalIR.Core.Utils

open import LogOS.Prelude.Bool using (Bool; true; false)
open import LogOS.Prelude.Maybe using (Maybe; just; nothing)
open import LogOS.Prelude.NatExtra using (+-zeroʳ)

-- 2) Untyped lambda calculus (de Bruijn) ------------------------------------

data Term : Set where
  var : ℕ → Term
  lam : Term → Term
  app : Term → Term → Term

-- Shift de Bruijn indices up/down by a natural amount, affecting vars ≥ cutoff.
shiftUp : ℕ → ℕ → Term → Term
shiftUp d cutoff (var k)   = if (cutoff ≤?ℕ k) then var (k + d) else var k
shiftUp d cutoff (lam t)   = lam (shiftUp d (suc cutoff) t)
shiftUp d cutoff (app t u) = app (shiftUp d cutoff t) (shiftUp d cutoff u)

shiftDown : ℕ → ℕ → Term → Term
shiftDown d cutoff (var k)   = if (cutoff ≤?ℕ k) then var (k ∸ d) else var k
shiftDown d cutoff (lam t)   = lam (shiftDown d (suc cutoff) t)
shiftDown d cutoff (app t u) = app (shiftDown d cutoff t) (shiftDown d cutoff u)

shiftUp-zero : ∀ cutoff t → shiftUp 0 cutoff t ≡ t
shiftUp-zero cutoff (var k) with cutoff ≤?ℕ k
... | true  = cong var (+-zeroʳ k)
... | false = refl
shiftUp-zero cutoff (lam t) = cong lam (shiftUp-zero (suc cutoff) t)
shiftUp-zero cutoff (app t u) =
  cong₂ app (shiftUp-zero cutoff t) (shiftUp-zero cutoff u)

shiftDown-zero : ∀ cutoff t → shiftDown 0 cutoff t ≡ t
shiftDown-zero cutoff (var k) with cutoff ≤?ℕ k
... | true  = cong var (minus-zeroʳ k)
... | false = refl
shiftDown-zero cutoff (lam t) = cong lam (shiftDown-zero (suc cutoff) t)
shiftDown-zero cutoff (app t u) =
  cong₂ app (shiftDown-zero cutoff t) (shiftDown-zero cutoff u)

-- Substitute variable j with s in t (de Bruijn).
substTerm : ℕ → Term → Term → Term
substTerm j s (var k) with k ==ℕ j
... | true  = s
... | false = var k
substTerm j s (lam t)   = lam (substTerm (suc j) (shiftUp 1 0 s) t)
substTerm j s (app t u) = app (substTerm j s t) (substTerm j s u)

beta : Term → Term → Term
beta t s = shiftDown 1 0 (substTerm 0 (shiftUp 1 0 s) t)

stepLam : Maybe Term → Maybe Term
stepLam (just t) = just (lam t)
stepLam nothing  = nothing

stepApp : Term → Term → Maybe Term → Maybe Term → Maybe Term
stepApp _ u (just t′) _          = just (app t′ u)
stepApp t _ nothing (just u′)    = just (app t u′)
stepApp _ _ nothing nothing      = nothing

stepAppTerm : Term → Term → Maybe Term → Maybe Term → Maybe Term
stepAppTerm (lam t) u _ _        = just (beta t u)
stepAppTerm (var k) u mt mu      = stepApp (var k) u mt mu
stepAppTerm (app t v) u mt mu    = stepApp (app t v) u mt mu

stepMaybeL : Term → Maybe Term
stepMaybeL (app t u) = stepAppTerm t u (stepMaybeL t) (stepMaybeL u)
stepMaybeL (lam t)   = stepLam (stepMaybeL t)
stepMaybeL (var _) = nothing

stepL : Term → Term
stepL t with stepMaybeL t
... | just t′ = t′
... | nothing = t

-- Small-step relation induced by `stepMaybeL`.

Step : Term → Term → Set
Step t t' = stepMaybeL t ≡ just t'

data Steps : Term → Term → Set where
  steps-refl : ∀ {t} → Steps t t
  steps-step : ∀ {t t' t''} → Step t t' → Steps t' t'' → Steps t t''

steps-trans : ∀ {t t' t''} → Steps t t' → Steps t' t'' → Steps t t''
steps-trans steps-refl steps₂ = steps₂
steps-trans (steps-step step₁ rest₁) steps₂ =
  steps-step step₁ (steps-trans rest₁ steps₂)

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

step-deterministic : ∀ {t u v} → Step t u → Step t v → u ≡ v
step-deterministic step₁ step₂ = just-inj (trans (sym step₁) step₂)

step-diamond : ∀ {t u v} → Step t u → Step t v → Steps u v
step-diamond {t = t} {u = u} {v = v} step₁ step₂
  rewrite step-deterministic {t = t} {u = u} {v = v} step₁ step₂
  = steps-refl

Normal : Term → Set
Normal t = stepMaybeL t ≡ nothing

stepL-normal : ∀ {t} → Normal t → stepL t ≡ t
stepL-normal eq rewrite eq = refl

stepL-step : ∀ {t u} → Step t u → stepL t ≡ u
stepL-step eq rewrite eq = refl

-- Church numerals (normal forms) for example decoding.

iterApp : ℕ → Term → Term → Term
iterApp zero    f x = x
iterApp (suc n) f x = app f (iterApp n f x)

church : ℕ → Term
church n = lam (lam (iterApp n (var 1) (var 0)))

countChurchBody : Term → ℕ
countChurchBody (app (var (suc zero)) t) = suc (countChurchBody t)
countChurchBody (app (var zero) _)            = zero
countChurchBody (app (var (suc (suc _))) _)   = zero
countChurchBody (app (lam _) _)               = zero
countChurchBody (app (app _ _) _)             = zero
countChurchBody (var _)          = zero
countChurchBody (lam _)          = zero

decodeChurch : Term → ℕ
decodeChurch (lam (lam body)) = countChurchBody body
decodeChurch (lam (var _))    = zero
decodeChurch (lam (app _ _))  = zero
decodeChurch (var _)          = zero
decodeChurch (app _ _)        = zero

record LambdaCode : Set where
  constructor mkL
  field term : Term

open LambdaCode public

stepLC : LambdaCode → LambdaCode
stepLC l = mkL (stepL (term l))

-- Observer-facing boundary (default: expose the term).

boundaryTerm : BoundaryObs LambdaCode
boundaryTerm = record { Obs = Term ; observe = term }

Effect : Set₁
Effect = EffectAt boundaryTerm

infix 4 _⊨_
_⊨_ : LambdaCode → Effect → Set
l ⊨ E = (l ⊨ᵇ boundaryTerm) E
