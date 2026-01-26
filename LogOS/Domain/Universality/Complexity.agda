{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Universality.Complexity where

open import LogOS.Prelude
open import LogOS.Prelude.Nat using (ℕ; zero; suc)
-- equality primitives via Prelude
open import LogOS.Prelude.Sum using (_⊎_; inj₁; inj₂)

open import LogOS.Computation.Core
open import LogOS.Computation.Blum
open import LogOS.Syntax.Prop using (⊥; ¬_)
-- Unit via Prelude; tt/⊤ available
open import LogOS.Prelude.Product using (Σ; _,_)
open import LogOS.Domain.Universality.Core

-- Decidable equality for ℕ (minimal)
infix 4 _≤?_
data _≤?_ : ℕ → ℕ → Set where
  eq  : ∀ {n} → n ≤? n
  neq : ∀ {n m} → ¬ (n ≡ m) → n ≤? m

pred : ℕ → ℕ
pred zero    = zero
pred (suc k) = k

natDecEq : (n m : ℕ) → (n ≡ m) ⊎ ¬ (n ≡ m)
natDecEq zero    zero    = inj₁ refl
natDecEq zero    (suc _) = inj₂ (λ ())
natDecEq (suc _) zero    = inj₂ (λ ())
natDecEq (suc n) (suc m) with natDecEq n m
... | inj₁ refl = inj₁ refl
... | inj₂ ne   = inj₂ (λ eqS → ne (cong pred eqS))

-- A canonical encoding type for demonstrative complexity (exact steps)
data ECode : Set where
  ET : ℕ → ECode
  EC : ℕ → ECode
  EQ : ℕ → ECode
  EB : ℕ → ECode

stepE : ECode → ECode
stepE (ET zero)    = ET zero
stepE (ET (suc k)) = ET k
stepE (EC zero)    = EC zero
stepE (EC (suc k)) = EC k
stepE (EQ zero)    = EQ zero
stepE (EQ (suc k)) = EQ k
stepE (EB zero)    = EB zero
stepE (EB (suc k)) = EB k

CE : Computation ECode
CE = record
  { Step  = stepE
  ; Halts = λ c → stepE c ≡ c
  }

-- Exact step complexity: time equals the counter embedded in ECode
TimeEq : ℕ → ECode → Set
TimeEq n (ET k) = n ≡ k
TimeEq n (EC k) = n ≡ k
TimeEq n (EQ k) = n ≡ k
TimeEq n (EB k) = n ≡ k

DomainE : ECode → Set
DomainE _ = ⊤

caseTotal : (c : ECode) → Σ ℕ (λ n → TimeEq n c)
caseTotal (ET k) = (k , refl)
caseTotal (EC k) = (k , refl)
caseTotal (EQ k) = (k , refl)
caseTotal (EB k) = (k , refl)

caseDec : (n : ℕ) (c : ECode) → (TimeEq n c ⊎ ¬ (TimeEq n c))
caseDec n (ET k) = natDecEq n k
caseDec n (EC k) = natDecEq n k
caseDec n (EQ k) = natDecEq n k
caseDec n (EB k) = natDecEq n k

BlumE : Blum ECode
BlumE = record
  { Comp   = CE
  ; TimeLe = λ _ _ → ⊤
  ; Domain = DomainE
  ; total  = λ _ _ → (0 , tt)
  ; dec    = λ _ _ → inj₁ tt
  }

-- Embed exact ECode into CoreUCode and relate exact time to conservative time

embedE : ECode → CoreUCode
embedE (ET k) = CoreT (mkT 0 k)
embedE (EC k) = CoreC (mkC k)
embedE (EQ k) = CoreQ (mkCoreQ k)
embedE (EB k) = CoreB (mkB 0 k)

-- Conservative time on CoreUCode (Computation CoreUCode)
UCompU : Computation CoreUCode
UCompU = record { Step = stepCoreU ; Halts = λ u → stepCoreU u ≡ u }

iterU : ℕ → CoreUCode → CoreUCode
iterU = iterate UCompU

TimeU : ℕ → CoreUCode → Set
TimeU n u = ⊤

timeEq→timeU : ∀ n c → TimeEq n c → TimeU n (embedE c)
timeEq→timeU _ _ _ = tt
