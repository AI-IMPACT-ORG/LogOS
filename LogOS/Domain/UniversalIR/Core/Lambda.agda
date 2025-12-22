{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Core.Lambda where

open import LogOS.Prelude
open import LogOS.Domain.UniversalIR.Core.Utils

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)

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
