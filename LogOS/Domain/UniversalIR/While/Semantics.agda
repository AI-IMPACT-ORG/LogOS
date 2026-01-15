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

-- Determinism: big-step evaluation yields a unique final store.

exec-deterministic
  : ∀ {s σ σ₁ σ₂}
  → Exec s σ σ₁
  → Exec s σ σ₂
  → σ₁ ≡ σ₂
exec-deterministic exec-skip exec-skip = refl
exec-deterministic exec-inc exec-inc = refl
exec-deterministic exec-dec exec-dec = refl
exec-deterministic exec-mulAB exec-mulAB = refl
exec-deterministic
  (exec-seq {t = t} {σ₁ = σ₁} {σ₂ = σ₂} e₁ e₂)
  (exec-seq {σ₁ = σ₁'} {σ₂ = σ₂'} e₁' e₂') =
  let
    ih₁ : σ₁ ≡ σ₁'
    ih₁ = exec-deterministic e₁ e₁'
    e₂'' : Exec t σ₁ σ₂'
    e₂'' = subst (λ σ' → Exec t σ' σ₂') (sym ih₁) e₂'
  in
  exec-deterministic e₂ e₂''
exec-deterministic (exec-while-zero eq₀) (exec-while-zero _) = refl
exec-deterministic (exec-while-zero eq₀) (exec-while-step eq₁ _ _) with trans (sym eq₀) eq₁
... | ()
exec-deterministic (exec-while-step eq₁ _ _) (exec-while-zero eq₀) with trans (sym eq₀) eq₁
... | ()
exec-deterministic
  (exec-while-step {v = v} {body = body} {σ₁ = σ₁} {σ₂ = σ₂} e q₁ q₂)
  (exec-while-step {σ₁ = σ₁'} {σ₂ = σ₂'} e' q₁' q₂') =
  let
    ih₁ : σ₁ ≡ σ₁'
    ih₁ = exec-deterministic q₁ q₁'
    q₂'' : Exec (whileNZ v body) σ₁ σ₂'
    q₂'' = subst (λ σ' → Exec (whileNZ v body) σ' σ₂') (sym ih₁) q₂'
  in
  exec-deterministic q₂ q₂''
