{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Encoding where

open import LogOS.Prelude

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)

-- Bit encodings used by UniversalIR.
--
-- Convention: little-endian bit lists (least significant bit first).

take : ∀ {A : Set} → ℕ → List A → List A
take zero    _        = []
take (suc _) []       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

length : ∀ {A : Set} → List A → ℕ
length []       = 0
length (_ ∷ xs) = suc (length xs)

double : ℕ → ℕ
double n = n + n

bitsToNat : List Bool → ℕ
bitsToNat []       = 0
bitsToNat (true ∷ bs)  = suc zero + double (bitsToNat bs)
bitsToNat (false ∷ bs) = double (bitsToNat bs)

incBits : List Bool → List Bool
incBits []             = true ∷ []
incBits (false ∷ bs)   = true ∷ bs
incBits (true  ∷ bs)   = false ∷ incBits bs

natToBits : ℕ → List Bool
natToBits zero    = []
natToBits (suc n) = incBits (natToBits n)

-- --------------------------------------------------------------------------
-- Small but high-leverage facts (used by the circuit view)

-- Addition lemma (right successor), kept local to avoid extra dependencies.
+-sucʳ-enc : ∀ m n → m + suc n ≡ suc (m + n)
+-sucʳ-enc zero    _ = refl
+-sucʳ-enc (suc m) n = cong suc (+-sucʳ-enc m n)

take-length : ∀ {A : Set} (xs : List A) → take (length xs) xs ≡ xs
take-length []       = refl
take-length (_ ∷ xs) = cong (_∷_ _) (take-length xs)

bitsToNat-incBits : ∀ ws → bitsToNat (incBits ws) ≡ suc (bitsToNat ws)
bitsToNat-incBits [] = refl
bitsToNat-incBits (false ∷ ws) = refl
bitsToNat-incBits (true ∷ ws) =
  let
    ih = bitsToNat-incBits ws
    n  = bitsToNat ws
    doubleSuc : double (suc n) ≡ suc (suc (double n))
    doubleSuc = cong suc (+-sucʳ-enc n n)
  in
  trans (cong double ih) doubleSuc

bitsToNat-natToBits : ∀ n → bitsToNat (natToBits n) ≡ n
bitsToNat-natToBits zero    = refl
bitsToNat-natToBits (suc n) =
  trans
    (bitsToNat-incBits (natToBits n))
    (cong suc (bitsToNat-natToBits n))
