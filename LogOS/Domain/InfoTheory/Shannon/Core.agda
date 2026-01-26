{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.InfoTheory.Shannon.Core where

open import LogOS.Prelude hiding (_+_; _*_)

open import LogOS.Prelude.Nat using (ℕ)
open import LogOS.Prelude.Fin using (Fin)
open import LogOS.Prelude.Product using (_×_; _,_)

open import LogOS.Domain.InfoTheory.Shannon.Facts

module For (F : ShannonFacts) where
  open ShannonFacts F

  -- Finite distributions over `Fin n`.
  record Dist (n : ℕ) : Set₁ where
    field
      p      : Fin n → ℝ
      p≥0    : ∀ i → 0# ≤ p i
      sum≡1  : sum p ≡ 1#

  -- Full-support distributions (strictly positive mass at every outcome).
  --
  -- This is kept separate from `Dist` so the library does not silently rule out
  -- zeros; derived theorems state positivity requirements explicitly.
  record DistPos (n : ℕ) : Set₁ where
    field
      dist : Dist n
      pPos : ∀ i → Pos (Dist.p dist i)
    open Dist dist public

  -- Finite KL divergence (as a total sum, relying on `klTerm`’s 0-extension).
  KL : ∀ {n : ℕ} → Dist n → Dist n → ℝ
  KL {n} P Q = sum (λ i → klTerm (Dist.p P i) (Dist.p Q i))

  -- Gibbs' inequality / non-negativity of KL, derived from log-sum inequality.
  --
  -- This is the first “real Shannon” theorem most applications want; it isolates
  -- the entire analytic burden into `logSumIneq` plus the interface laws of the facts pack.
  KL≥0 : ∀ {n : ℕ} (P : Dist n) (Q : DistPos n) → 0# ≤ KL P (DistPos.dist Q)
  KL≥0 {n} P Q =
    subst
      (λ x → x ≤ KL P (DistPos.dist Q))
      rhs≡0
      (logSumIneq (Dist.p P) (DistPos.p Q) (Dist.p≥0 P) (DistPos.pPos Q))
    where
      rhs≡0 : klTerm (sum (Dist.p P)) (sum (DistPos.p Q)) ≡ 0#
      rhs≡0 =
        trans
          (cong₂ klTerm (Dist.sum≡1 P) (DistPos.sum≡1 Q))
          klTerm11≡0

  -- Shannon entropy (as “negative self-KL term”, i.e. -Σ p ln p with 0-extension).
  H : ∀ {n : ℕ} → Dist n → ℝ
  H {n} P = - (sum (λ i → klTerm (Dist.p P i) 1#))

  -- Stochastic matrices / Markov kernels (row-stochastic).
  record Kernel (m n : ℕ) : Set₁ where
    field
      K      : Fin m → Fin n → ℝ
      K≥0    : ∀ i j → 0# ≤ K i j
      rowSum≡1 : ∀ i → sum (K i) ≡ 1#

  -- Strictly-positive kernels (every entry is positive).
  record KernelPos (m n : ℕ) : Set₁ where
    field
      ker   : Kernel m n
      rowPos : ∀ i j → Pos (Kernel.K ker i j)
    open Kernel ker public

  -- Pushforward of a distribution along a kernel (finite Markov evolution).
  push : ∀ {m n : ℕ} → Kernel m n → Dist m → (Fin n → ℝ)
  push {m} {n} K P j = sum (λ i → Dist.p P i * Kernel.K K i j)

  sum≥0
    : ∀ {n : ℕ} (f : Fin n → ℝ)
    → (∀ i → 0# ≤ f i)
    → 0# ≤ sum f
  sum≥0 {n} f f≥0 =
    let
      le : sum (λ (_ : Fin n) → 0#) ≤ sum f
      le = sum-mono (λ i → f≥0 i)
    in
    subst (λ z → z ≤ sum f) (FiniteSum.sum0 sumPack {n = n}) le

  -- Pushforward closes on `Dist` (finite case), derived from the facts pack.
  --
  -- This is the canonical “Markov pushforward is a distribution” lemma:
  -- - nonnegativity is transported through `≤0-*` and `sum-mono` + `sum0`,
  -- - normalization uses `sum-swap` + `sum-*ˡ` + row-stochasticity.

  pushDist
    : ∀ {m n : ℕ}
      → Kernel m n
      → Dist m
      → Dist n
  pushDist {m} {n} K P =
    record
      { p     = push K P
      ; p≥0   = p≥0
      ; sum≡1 = sum≡1
      }
    where
      p≥0 : ∀ j → 0# ≤ push K P j
      p≥0 j =
        let
          f : Fin m → ℝ
          f i = Dist.p P i * Kernel.K K i j

          f≥0 : ∀ i → 0# ≤ f i
          f≥0 i = ≤0-* (Dist.p≥0 P i) (Kernel.K≥0 K i j)
        in
        sum≥0 f f≥0

      sum≡1 : sum (push K P) ≡ 1#
      sum≡1 =
        let
          rowNorm
            : ∀ i
            → sum (λ j → Dist.p P i * Kernel.K K i j) ≡ Dist.p P i
          rowNorm i =
            trans
              (sum-*ˡ (Dist.p P i) (Kernel.K K i))
              (trans
                (cong (λ x → Dist.p P i * x) (Kernel.rowSum≡1 K i))
                (*-idr (Dist.p P i)))
        in
        trans
          (sym (sum-swap (λ i j → Dist.p P i * Kernel.K K i j)))
          (trans
            (sum-cong rowNorm)
            (Dist.sum≡1 P))

  -- Strict positivity is preserved by strictly-positive kernels.
  --
  -- This is the smallest additional “physics meaning” lemma needed for treating
  -- kernels as genuine channels on full-support distributions (no silent zeros).
  pushDistPos
    : ∀ {m n : ℕ}
      → KernelPos m n
      → DistPos m
      → DistPos n
  pushDistPos {m} {n} K P =
    record
      { dist = pushDist (KernelPos.ker K) (DistPos.dist P)
      ; pPos = pPos
      }
    where
      pPos : ∀ j → Pos (Dist.p (pushDist (KernelPos.ker K) (DistPos.dist P)) j)
      pPos j =
        let
          f : Fin m → ℝ
          f i = DistPos.p P i * Kernel.K (KernelPos.ker K) i j

          fPos : ∀ i → Pos (f i)
          fPos i = Pos-* (DistPos.pPos P i) (KernelPos.rowPos K i j)
        in
        sumPos f fPos
