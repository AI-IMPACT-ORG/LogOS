{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.While.Semantics where

open import LogOS.Prelude

open import LogOS.Domain.UniversalIR.While.Language

-- Store for the two variables A and B.

record Store : Set where
  constructor ⟨_,_⟩
  field
    a b : ℕ

open Store public

get : Var → Store → ℕ
get A σ = a σ
get B σ = b σ

set : Var → ℕ → Store → Store
set A n σ = ⟨ n , b σ ⟩
set B n σ = ⟨ a σ , n ⟩

stepInc : Var → Store → Store
stepInc v σ = set v (suc (get v σ)) σ

decℕ : ℕ → ℕ
decℕ zero    = zero
decℕ (suc n) = n

stepDec : Var → Store → Store
stepDec v σ = set v (decℕ (get v σ)) σ

stepMulAB : Store → Store
stepMulAB σ = ⟨ (a σ) * (b σ) , b σ ⟩

-- Big-step terminating semantics (inductive: only finite runs exist as proofs).

data Exec : Stmt → Store → Store → Set where
  exec-skip : ∀ {σ} → Exec skip σ σ

  exec-inc : ∀ {v σ} → Exec (inc v) σ (stepInc v σ)

  exec-dec : ∀ {v σ} → Exec (dec v) σ (stepDec v σ)

  exec-mulAB : ∀ {σ} → Exec mulAB σ (stepMulAB σ)

  exec-seq :
    ∀ {s t σ σ₁ σ₂} →
    Exec s σ σ₁ →
    Exec t σ₁ σ₂ →
    Exec (s >> t) σ σ₂

  exec-while-zero :
    ∀ {v body σ} →
    get v σ ≡ 0 →
    Exec (whileNZ v body) σ σ

  exec-while-step :
    ∀ {v body σ σ₁ σ₂ n} →
    get v σ ≡ suc n →
    Exec body σ σ₁ →
    Exec (whileNZ v body) σ₁ σ₂ →
    Exec (whileNZ v body) σ σ₂
