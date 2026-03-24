{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.Core where

-- Shared, stdlib-free primitives for the Set.MM parser/interpretation pipeline.
-- (Keeps the stage modules small and transformer-aligned.)

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ; zero; suc)
open import LogOS.Prelude.List using (List; []; _∷_)
import LogOS.Prelude.List.Ops as ListOps

-- Bounded natural index, used for total database projections.
data Fin : ℕ → Set where
  fzero : ∀ {n} → Fin (suc n)
  fsuc : ∀ {n} → Fin n → Fin (suc n)

-- --------------------------------------------------------------------------
-- Minimal local Maybe (stdlib-free).

data Maybe {ℓ : Level} (A : Set ℓ) : Set ℓ where
  nothing : Maybe A
  just    : A → Maybe A

Unit : Set
Unit = ⊤ {lzero}

infixl 1 _>>=_
_>>=_ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → Maybe A → (A → Maybe B) → Maybe B
nothing >>= _ = nothing
just x  >>= f = f x

infixl 3 _<|>_
_<|>_ : ∀ {ℓ} {A : Set ℓ} → Maybe A → Maybe A → Maybe A
nothing <|> mb = mb
just x  <|> _  = just x

mapMaybe : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → Maybe A → Maybe B
mapMaybe f nothing = nothing
mapMaybe f (just x) = just (f x)

mapMaybeList : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'}
  → (A → Maybe B)
  → List A
  → Maybe (List B)
mapMaybeList f [] = just []
mapMaybeList f (x ∷ xs) =
  f x >>= λ y →
  mapMaybeList f xs >>= λ ys →
  just (y ∷ ys)

-- --------------------------------------------------------------------------
-- List and helper utilities.

infixr 6 _++_
_++_ : ∀ {ℓ} {A : Set ℓ} → List A → List A → List A
_++_ = ListOps._++_

map : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → List A → List B
map = ListOps.map

len : ∀ {ℓ} {A : Set ℓ} → List A → ℕ
len [] = zero
len (_ ∷ xs) = suc (len xs)

reverse : ∀ {ℓ} {A : Set ℓ} → List A → List A
reverse xs = go xs []
  where
    go : ∀ {ℓ} {A : Set ℓ} → List A → List A → List A
    go [] acc = acc
    go (x ∷ xs) acc = go (xs) (x ∷ acc)

record Snoc {ℓ} (A : Set ℓ) : Set ℓ where
  constructor snoc
  field
    init : List A
    last : A

unsnoc : ∀ {ℓ} {A : Set ℓ} → List A → Maybe (Snoc A)
unsnoc [] = nothing
unsnoc (x ∷ xs) = go [] x xs
  where
    go : ∀ {ℓ} {A : Set ℓ} → List A → A → List A → Maybe (Snoc A)
    go acc y [] = just (snoc (reverse acc) y)
    go acc y (z ∷ zs) = go (y ∷ acc) z zs

-- --------------------------------------------------------------------------
-- Nat comparison helpers.

data Cmp : Set where
  less equal greater : Cmp

cmpNat : ℕ → ℕ → Cmp
cmpNat zero zero = equal
cmpNat zero (suc _) = less
cmpNat (suc _) zero = greater
cmpNat (suc m) (suc n) = cmpNat m n

predNat : ℕ → ℕ
predNat zero = zero
predNat (suc n) = n

-- Lookup a token in an environment list and return its De Bruijn index.
lookupIx : ℕ → List ℕ → Maybe ℕ
lookupIx x env = go zero env
  where
    go : ℕ → List ℕ → Maybe ℕ
    go _ [] = nothing
    go i (y ∷ ys) with cmpNat x y
    ... | equal = just i
    ... | less = go (suc i) ys
    ... | greater = go (suc i) ys

-- Membership test (as Maybe with a useless witness).
contains : ℕ → List ℕ → Maybe Unit
contains x xs with lookupIx x xs
... | nothing = nothing
... | just _  = just tt

-- Remove duplicates from a list of variables, keeping the last occurrence.
dedup : List ℕ → List ℕ
dedup [] = []
dedup (x ∷ xs) with contains x xs
... | nothing = x ∷ dedup xs
... | just _ = dedup xs

-- Safe list lookup by de Bruijn-like index.
lookupAt : ∀ {ℓ} {A : Set ℓ} → ℕ → List A → Maybe A
lookupAt _ [] = nothing
lookupAt zero (x ∷ _) = just x
lookupAt (suc n) (_ ∷ xs) = lookupAt n xs

-- Safe total lookup using a bounded index.
lookupFin : ∀ {ℓ} {A : Set ℓ} {xs : List A} → Fin (len xs) → A
lookupFin {xs = []} ()
lookupFin {xs = x ∷ xs} fzero = x
lookupFin {xs = x ∷ xs} (fsuc i) = lookupFin {xs = xs} i
