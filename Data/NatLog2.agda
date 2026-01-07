{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module Data.NatLog2 where

open import LogOS.Prelude

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.NatOrder using
  ( _≤ℕ_
  ; z≤n
  ; s≤s
  ; ≤ℕ-refl
  ; trans≤ℕ
  ; weakenRight
  ; dec≤ℕ
  ; not≤→≥
  ; split≤suc
  ; ¬suc≤self
  ; antisym≤ℕ
  )
open import Data.NatExtra using (+-zeroʳ; +-sucʳ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import LogOS.Syntax.Prop using (¬_; ⊥; ⊥-elim)

one : ℕ
one = suc zero

two : ℕ
two = suc one

-- Right-recursive addition and multiplication on ℕ.
--
-- We prefer these over the primitive operators because monotonicity proofs
-- against `Data.NatOrder._≤ℕ_` become straightforward.

plusR : ℕ → ℕ → ℕ
plusR a zero    = a
plusR a (suc n) = suc (plusR a n)

plusR-assoc : ∀ a b c → plusR a (plusR b c) ≡ plusR (plusR a b) c
plusR-assoc a b zero = refl
plusR-assoc a b (suc c) = cong suc (plusR-assoc a b c)

plusR-zeroˡ : ∀ a → plusR zero a ≡ a
plusR-zeroˡ zero = refl
plusR-zeroˡ (suc a) = cong suc (plusR-zeroˡ a)

plusR-sucˡ : ∀ a b → plusR (suc a) b ≡ suc (plusR a b)
plusR-sucˡ a zero = refl
plusR-sucˡ a (suc b) = cong suc (plusR-sucˡ a b)

plusR-comm : ∀ a b → plusR a b ≡ plusR b a
plusR-comm a zero =
  trans refl (sym (plusR-zeroˡ a))
plusR-comm a (suc b) =
  trans (cong suc (plusR-comm a b)) (sym (plusR-sucˡ b a))

plusR≡+ : ∀ a b → plusR a b ≡ a + b
plusR≡+ a zero = sym (+-zeroʳ a)
plusR≡+ a (suc b) =
  trans (cong suc (plusR≡+ a b)) (sym (+-sucʳ a b))

mul : ℕ → ℕ → ℕ
mul _ zero    = zero
mul a (suc n) = plusR a (mul a n)

mul-dist-plusR : ∀ a b c → mul a (plusR b c) ≡ plusR (mul a b) (mul a c)
mul-dist-plusR a b zero = refl
mul-dist-plusR a b (suc c) =
  trans
    (cong (plusR a) (mul-dist-plusR a b c))
    (trans
      (plusR-assoc a (mul a b) (mul a c))
      (trans
        (cong (λ x → plusR x (mul a c)) (plusR-comm a (mul a b)))
        (sym (plusR-assoc (mul a b) a (mul a c)))))

mul-assoc : ∀ a b c → mul a (mul b c) ≡ mul (mul a b) c
mul-assoc a b zero = refl
mul-assoc a b (suc c) =
  trans
    (mul-dist-plusR a b (mul b c))
    (cong (plusR (mul a b)) (mul-assoc a b c))

-- Base-2 exponentiation on ℕ (as repeated doubling).
exp₂ : ℕ → ℕ
exp₂ zero    = one
exp₂ (suc k) = plusR (exp₂ k) (exp₂ k)

one≤suc : ∀ n → one ≤ℕ suc n
one≤suc n = s≤s z≤n

exp₂-stepMul : ∀ k → exp₂ (suc k) ≡ mul (exp₂ k) two
exp₂-stepMul _ = refl

-- Basic order lemmas for `plusR` / `mul` -----------------------------------

plusR-monoL : ∀ {a b} → a ≤ℕ b → ∀ c → plusR a c ≤ℕ plusR b c
plusR-monoL ab zero = ab
plusR-monoL ab (suc c) = s≤s (plusR-monoL ab c)

lePlusR : ∀ a c → a ≤ℕ plusR a c
lePlusR a zero = ≤ℕ-refl
lePlusR a (suc c) = weakenRight (lePlusR a c)

plusR-monoR : ∀ {c d} → c ≤ℕ d → ∀ a → plusR a c ≤ℕ plusR a d
plusR-monoR {d = d} z≤n a = lePlusR a d
plusR-monoR (s≤s cd) a = s≤s (plusR-monoR cd a)

mul-monoL : ∀ {a b} → a ≤ℕ b → ∀ c → mul a c ≤ℕ mul b c
mul-monoL ab zero = ≤ℕ-refl
mul-monoL {a = a} {b = b} ab (suc c) =
  trans≤ℕ
    (plusR-monoL ab (mul a c))
    (plusR-monoR (mul-monoL ab c) b)

mul-monoR : ∀ a {c d} → c ≤ℕ d → mul a c ≤ℕ mul a d
mul-monoR a z≤n = z≤n
mul-monoR a (s≤s cd) = plusR-monoR (mul-monoR a cd) a

mul-mono₂ : ∀ {a b c d} → a ≤ℕ b → c ≤ℕ d → mul a c ≤ℕ mul b d
mul-mono₂ {b = b} {c = c} ab cd =
  trans≤ℕ (mul-monoL ab c) (mul-monoR b cd)

-- `exp₂ k` is always a successor (hence nonzero).
exp₂-suc : ∀ k → Σ ℕ (λ t → exp₂ k ≡ suc t)
exp₂-suc zero = 0 , refl
exp₂-suc (suc k) with exp₂-suc k
... | t , eq rewrite eq =
  plusR (suc t) t , refl

-- A very coarse lower bound: k ≤ 2^k (enough to bound search depth).
k≤exp₂k : ∀ k → k ≤ℕ exp₂ k
k≤exp₂k zero = z≤n
k≤exp₂k (suc k) =
  trans≤ℕ (s≤s (k≤exp₂k k)) (suc≤double (exp₂ k) (proj₁ (exp₂-suc k)) (proj₂ (exp₂-suc k)))
  where
    suc≤double : ∀ a t → a ≡ suc t → suc a ≤ℕ plusR a a
    suc≤double a t a≡ with a≡
    ... | refl =
      s≤s (lePlusR (suc t) t)

-- `exp₂` is monotone w.r.t. `≤ℕ`.
exp₂-mono : ∀ {a b} → a ≤ℕ b → exp₂ a ≤ℕ exp₂ b
exp₂-mono {a = zero} {b} z≤n with exp₂-suc b
... | t , eq rewrite eq = s≤s z≤n
exp₂-mono (s≤s ab) =
  -- exp₂ (suc a) = exp₂ a + exp₂ a, and `plusR` is monotone in both slots.
  let ih = exp₂-mono ab in
  trans≤ℕ (plusR-monoL ih _) (plusR-monoR ih _)

-- Multiplicativity (with respect to `mul`) over right-recursive addition.
exp₂-plusR : ∀ a b → exp₂ (plusR a b) ≡ mul (exp₂ a) (exp₂ b)
exp₂-plusR a zero = refl
exp₂-plusR a (suc b) =
  trans
    (exp₂-stepMul (plusR a b))
    (trans
      (cong (λ x → mul x two) (exp₂-plusR a b))
      (trans
        (sym (mul-assoc (exp₂ a) (exp₂ b) two))
        (cong (mul (exp₂ a)) (sym (exp₂-stepMul b)))))

-- Same statement for the primitive `_+_` (via `plusR≡+`).
exp₂-+ : ∀ a b → exp₂ (a + b) ≡ mul (exp₂ a) (exp₂ b)
exp₂-+ a b =
  trans (cong exp₂ (sym (plusR≡+ a b))) (exp₂-plusR a b)

-- A bounded maximum search for floor log₂ on a positive bound `suc n`.
--
-- `maxFits n d` returns the maximum `k ≤ d` such that `2^k ≤ suc n`.
maxFits : (n d : ℕ) → ℕ
maxFits n zero = 0
maxFits n (suc d) with dec≤ℕ (exp₂ (suc d)) (suc n)
... | inj₁ _ = suc d
... | inj₂ _ = maxFits n d

maxFits-sound : ∀ n d → exp₂ (maxFits n d) ≤ℕ suc n
maxFits-sound n zero = one≤suc n
maxFits-sound n (suc d) with dec≤ℕ (exp₂ (suc d)) (suc n)
... | inj₁ fits = fits
... | inj₂ _ = maxFits-sound n d

maxFits-max
  : ∀ n d k
    → k ≤ℕ d
    → exp₂ k ≤ℕ suc n
    → k ≤ℕ maxFits n d
maxFits-max n zero zero z≤n _ = z≤n
maxFits-max n zero (suc k) () _
maxFits-max n (suc d) k k≤sd fits with dec≤ℕ (exp₂ (suc d)) (suc n)
... | inj₁ _ =
  -- If the top exponent fits, it is the maximum.
  k≤sd
... | inj₂ notTop with split≤suc k≤sd
... | inj₁ k≤d =
  maxFits-max n d k k≤d fits
... | inj₂ k≡sd =
  ⊥-elim (notTop (subst (λ x → exp₂ x ≤ℕ suc n) k≡sd fits))

-- A total, safe base-2 log on ℕ, with the convention log₂(0) = 0.
log₂ : ℕ → ℕ
log₂ zero    = 0
log₂ (suc n) = maxFits n (suc n)

-- Soundness: for positive n, 2^(log₂ n) ≤ n.
exp₂-log₂≤ : ∀ n → exp₂ (log₂ (suc n)) ≤ℕ suc n
exp₂-log₂≤ n = maxFits-sound n (suc n)

-- Maximality: if `2^k` fits under `n`, then `k` is bounded by `log₂ n`.
log₂-max : ∀ {n k} → exp₂ k ≤ℕ n → k ≤ℕ log₂ n
log₂-max {n = zero} {k} fits with exp₂-suc k
... | t , eq rewrite eq =
  ⊥-elim (notSuc≤0 fits)
  where
    notSuc≤0 : ∀ {m} → ¬ (suc m ≤ℕ zero)
    notSuc≤0 ()
log₂-max {n = suc n} {k} fits =
  maxFits-max n (suc n) k k≤ fits
  where
    k≤ : k ≤ℕ suc n
    k≤ = trans≤ℕ (k≤exp₂k k) fits

-- Monotonicity: floor log₂ is monotone w.r.t. `≤ℕ`.
log₂-mono : ∀ {m n} → m ≤ℕ n → log₂ m ≤ℕ log₂ n
log₂-mono {m = zero} {_} _ = z≤n
log₂-mono {m = suc m} {n} m≤n =
  log₂-max (trans≤ℕ (exp₂-log₂≤ m) m≤n)

-- The other half of the (floor log, exp) adjunction on positive naturals:
-- if k ≤ log₂ n, then 2^k ≤ n.
≤log₂→exp₂≤ : ∀ {n k} → k ≤ℕ log₂ (suc n) → exp₂ k ≤ℕ suc n
≤log₂→exp₂≤ {n} k≤ =
  trans≤ℕ (exp₂-mono k≤) (exp₂-log₂≤ n)

-- Key normal form: log₂(2^k) = k (with our convention log₂ 0 = 0).
--
-- This is what lets us turn “outcome-count ≤ 2^(budget)” bounds into “bits ≤ budget”.
log₂-exp₂ : ∀ k → log₂ (exp₂ k) ≡ k
log₂-exp₂ k = antisym≤ℕ (log₂-exp₂≤ k) (log₂-exp₂≥ k)
  where
    log₂-exp₂≥ : ∀ k → k ≤ℕ log₂ (exp₂ k)
    log₂-exp₂≥ k = log₂-max {n = exp₂ k} {k = k} ≤ℕ-refl

    strict-exp₂ : ∀ k → ¬ (exp₂ (suc k) ≤ℕ exp₂ k)
    strict-exp₂ k le =
      ¬suc≤self (trans≤ℕ (suc≤double (exp₂ k) (proj₁ (exp₂-suc k)) (proj₂ (exp₂-suc k))) le)
      where
        suc≤double : ∀ a t → a ≡ suc t → suc a ≤ℕ plusR a a
        suc≤double a t a≡ with a≡
        ... | refl = s≤s (lePlusR (suc t) t)

    notSuc≤-log₂-exp₂
      : ∀ k t → exp₂ k ≡ suc t → ¬ (suc k ≤ℕ log₂ (suc t))
    notSuc≤-log₂-exp₂ k t eq sk≤L =
      strict-exp₂ k
        (subst
          (λ x → exp₂ (suc k) ≤ℕ x)
          (sym eq)
          (≤log₂→exp₂≤ {n = t} sk≤L))

    log₂-exp₂≤ : ∀ k → log₂ (exp₂ k) ≤ℕ k
    log₂-exp₂≤ k with exp₂-suc k
    ... | t , eq rewrite eq with split≤suc (not≤→≥ (notSuc≤-log₂-exp₂ k t eq))
    ... | inj₁ L≤k  = L≤k
    ... | inj₂ L≡sk =
      ⊥-elim
        (notSuc≤-log₂-exp₂ k t eq
          (subst (λ x → suc k ≤ℕ x) (sym L≡sk) ≤ℕ-refl))

-- (Product law lemmas live in `LogOS.Domain.Complexity.HartleyEntropy`,
-- where we can choose the intended multiplication notion per application.)
