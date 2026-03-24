{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Proof.Syntax where

open import LogOS.Prelude
open import LogOS.Host.Nat using (ℕ; zero; suc)

-- First-order term language for the ZF constructor surface.

infix 50 var
infixl 40 pairT
infixl 35 _∈F_ _≈F_
infixr 30 _⇒_
infixr 25 _∧F_
infixr 24 _∨F_
infixr 23 _↔F_

data Term : Set where
  var    : ℕ → Term
  emptyT : Term
  pairT  : Term → Term → Term
  unionT : Term → Term
  powerT : Term → Term
  succT  : Term → Term
  omegaT : Term

data Formula : Set where
  ⊥F    : Formula
  _∈F_  : Term → Term → Formula
  _≈F_  : Term → Term → Formula
  _⇒_   : Formula → Formula → Formula
  _∧F_  : Formula → Formula → Formula
  _∨F_  : Formula → Formula → Formula
  _↔F_  : Formula → Formula → Formula
  ∀F    : Formula → Formula
  ∃F    : Formula → Formula

-- Small de Bruijn aliases for presentation-facing formulas.
v0 : Term
v0 = var zero

v1 : Term
v1 = var (suc zero)

v2 : Term
v2 = var (suc (suc zero))

v3 : Term
v3 = var (suc (suc (suc zero)))

¬F : Formula → Formula
¬F φ = φ ⇒ ⊥F

⊤F : Formula
⊤F = ⊥F ⇒ ⊥F

-- De Bruijn renaming utilities.

Renaming : Set
Renaming = ℕ → ℕ

liftRen : Renaming → Renaming
liftRen ρ zero = zero
liftRen ρ (suc n) = suc (ρ n)

renameTerm : Renaming → Term → Term
renameTerm ρ (var n) = var (ρ n)
renameTerm ρ emptyT = emptyT
renameTerm ρ (pairT t u) = pairT (renameTerm ρ t) (renameTerm ρ u)
renameTerm ρ (unionT t) = unionT (renameTerm ρ t)
renameTerm ρ (powerT t) = powerT (renameTerm ρ t)
renameTerm ρ (succT t) = succT (renameTerm ρ t)
renameTerm ρ omegaT = omegaT

renameFormula : Renaming → Formula → Formula
renameFormula ρ ⊥F = ⊥F
renameFormula ρ (t ∈F u) = renameTerm ρ t ∈F renameTerm ρ u
renameFormula ρ (t ≈F u) = renameTerm ρ t ≈F renameTerm ρ u
renameFormula ρ (φ ⇒ ψ) = renameFormula ρ φ ⇒ renameFormula ρ ψ
renameFormula ρ (φ ∧F ψ) = renameFormula ρ φ ∧F renameFormula ρ ψ
renameFormula ρ (φ ∨F ψ) = renameFormula ρ φ ∨F renameFormula ρ ψ
renameFormula ρ (φ ↔F ψ) = renameFormula ρ φ ↔F renameFormula ρ ψ
renameFormula ρ (∀F φ) = ∀F (renameFormula (liftRen ρ) φ)
renameFormula ρ (∃F φ) = ∃F (renameFormula (liftRen ρ) φ)

-- Insert a new variable at index 1 (preserve 0, shift ≥1 by +1).

insert1Ren : Renaming
insert1Ren zero = zero
insert1Ren (suc n) = suc (suc n)

-- Insert two new variables after index 0 (preserve 0, shift ≥1 by +2).

insert2Ren : Renaming
insert2Ren zero = zero
insert2Ren (suc n) = suc (suc (suc n))

-- Swap the two innermost variables (0 ↔ 1), keep ≥2 fixed.
swap01Ren : Renaming
swap01Ren zero = suc zero
swap01Ren (suc zero) = zero
swap01Ren (suc (suc n)) = suc (suc n)

-- Insert one new variable after index 1 (preserve 0 and 1, shift ≥2 by +1).
insertAfter1Ren : Renaming
insertAfter1Ren zero = zero
insertAfter1Ren (suc zero) = suc zero
insertAfter1Ren (suc (suc n)) = suc (suc (suc n))

-- Insert two new variables after index 1 (preserve 0 and 1, shift ≥2 by +2).
insertAfter1By2Ren : Renaming
insertAfter1By2Ren zero = zero
insertAfter1By2Ren (suc zero) = suc zero
insertAfter1By2Ren (suc (suc n)) = suc (suc (suc (suc n)))

liftAfter0Term : Term → Term
liftAfter0Term = renameTerm insert1Ren

liftAfter0Formula : Formula → Formula
liftAfter0Formula = renameFormula insert1Ren

liftAfter0By2Term : Term → Term
liftAfter0By2Term = renameTerm insert2Ren

-- Single-binder substitution interface.

liftTerm : Term → Term
liftTerm (var n) = var (suc n)
liftTerm emptyT = emptyT
liftTerm (pairT t u) = pairT (liftTerm t) (liftTerm u)
liftTerm (unionT t) = unionT (liftTerm t)
liftTerm (powerT t) = powerT (liftTerm t)
liftTerm (succT t) = succT (liftTerm t)
liftTerm omegaT = omegaT

-- Weakening by one variable (binder-aware shift): insert a fresh variable 0.
liftFormula : Formula → Formula
liftFormula = renameFormula suc

-- Capture-avoiding substitution of a term for de Bruijn variable `k`
-- (and dropping that variable from the context).
data Cmp : Set where
  less equal greater : Cmp

cmpNat : ℕ → ℕ → Cmp
cmpNat zero zero = equal
cmpNat zero (suc n) = less
cmpNat (suc n) zero = greater
cmpNat (suc n) (suc k) = cmpNat n k

predNat : ℕ → ℕ
predNat zero = zero
predNat (suc n) = n

substVarAt : ℕ → Term → ℕ → Term
substVarAt k s n with cmpNat n k
... | less = var n
... | equal = s
... | greater = var (predNat n)

substTermAt : ℕ → Term → Term → Term
substTermAt k s (var n) = substVarAt k s n
substTermAt k s emptyT = emptyT
substTermAt k s (pairT t u) = pairT (substTermAt k s t) (substTermAt k s u)
substTermAt k s (unionT t) = unionT (substTermAt k s t)
substTermAt k s (powerT t) = powerT (substTermAt k s t)
substTermAt k s (succT t) = succT (substTermAt k s t)
substTermAt k s omegaT = omegaT

substFormulaAt : ℕ → Term → Formula → Formula
substFormulaAt k s ⊥F = ⊥F
substFormulaAt k s (t ∈F u) = substTermAt k s t ∈F substTermAt k s u
substFormulaAt k s (t ≈F u) = substTermAt k s t ≈F substTermAt k s u
substFormulaAt k s (φ ⇒ ψ) = substFormulaAt k s φ ⇒ substFormulaAt k s ψ
substFormulaAt k s (φ ∧F ψ) = substFormulaAt k s φ ∧F substFormulaAt k s ψ
substFormulaAt k s (φ ∨F ψ) = substFormulaAt k s φ ∨F substFormulaAt k s ψ
substFormulaAt k s (φ ↔F ψ) = substFormulaAt k s φ ↔F substFormulaAt k s ψ
substFormulaAt k s (∀F φ) = ∀F (substFormulaAt (suc k) (liftTerm s) φ)
substFormulaAt k s (∃F φ) = ∃F (substFormulaAt (suc k) (liftTerm s) φ)

subst0Term : Term → Term → Term
subst0Term = substTermAt zero

subst0Formula : Term → Formula → Formula
subst0Formula = substFormulaAt zero
