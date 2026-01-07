{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.HartleyEntropy where

open import LogOS.Prelude

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.NatOrder using (_≤ℕ_)
open import Data.NatLog2 using
  ( exp₂
  ; log₂
  ; exp₂-log₂≤
  ; log₂-exp₂
  ; log₂-mono
  ; log₂-max
  ; mul
  ; mul-mono₂
  ; exp₂-+
  )

-- Hartley entropy in bits: H₀(X) = log₂ |X|.
-- (This is the “uniform” / counting entropy; it is fully computable and provable
-- in the current `--no-libraries` kernel without extra analytic axioms.)
H₀ : ℕ → ℕ
H₀ = log₂

H₀-mono : ∀ {m n} → m ≤ℕ n → H₀ m ≤ℕ H₀ n
H₀-mono = log₂-mono

-- Sanity: for positive cardinalities, the number of distinguishable states
-- implied by H₀ fits in the original count.
exp₂-H₀≤ : ∀ n → exp₂ (H₀ (suc n)) ≤ℕ suc n
exp₂-H₀≤ = exp₂-log₂≤

-- Exact “bits behave like bits” law: log₂(2^k) = k.
H₀-exp₂ : ∀ k → H₀ (exp₂ k) ≡ k
H₀-exp₂ = log₂-exp₂

-- Exact additivity on power-of-two state spaces.
--
-- Reading: if two independent registers have 2^a and 2^b possible states, the
-- combined register has 2^(a+b) states, hence (Hartley) bits add.
H₀-mul-exp₂ : ∀ a b → H₀ (mul (exp₂ a) (exp₂ b)) ≡ a + b
H₀-mul-exp₂ a b =
  trans
    (cong H₀ (sym (exp₂-+ a b)))
    (H₀-exp₂ (a + b))

-- Product law (one direction, provable without extra arithmetic infrastructure):
-- combining independent finite state spaces cannot decrease Hartley entropy.
H₀-mul-super : ∀ a b → (H₀ (suc a) + H₀ (suc b)) ≤ℕ H₀ (mul (suc a) (suc b))
H₀-mul-super a b =
  log₂-max
    (subst
      (λ x → x ≤ℕ mul (suc a) (suc b))
      (sym (exp₂-+ ha hb))
      (mul-mono₂ (exp₂-H₀≤ a) (exp₂-H₀≤ b)))
  where
    ha : ℕ
    ha = H₀ (suc a)

    hb : ℕ
    hb = H₀ (suc b)
