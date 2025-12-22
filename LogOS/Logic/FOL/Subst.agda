{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Logic.FOL.Subst where

open import LogOS.Prelude

open import Data.Fin using (Fin; fzero; fsuc)
open import Data.List using (List; map)

open import LogOS.Logic.FOL.Syntax

-- Renamings (de Bruijn) and the induced action on terms/formulas/contexts.

Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n

wkRen : ∀ {n} → Ren n (suc n)
wkRen = fsuc

liftRen : ∀ {m n} → Ren m n → Ren (suc m) (suc n)
liftRen ρ fzero    = fzero
liftRen ρ (fsuc i) = fsuc (ρ i)

renameTerm : ∀ {m n} → Ren m n → Term m → Term n
renameTerm ρ x = ρ x

renameFml : ∀ {ℓ} {Σ : Signature {ℓ}} {m n} → Ren m n → Fml Σ m → Fml Σ n
renameFml ρ ⊥ᶠ             = ⊥ᶠ
renameFml ρ (pred p x)       = pred p (renameTerm ρ x)
renameFml ρ (rel₂ r x y)     = rel₂ r (renameTerm ρ x) (renameTerm ρ y)
renameFml ρ (φ ⇒ ψ)          = renameFml ρ φ ⇒ renameFml ρ ψ
renameFml ρ (φ ∧ ψ)          = renameFml ρ φ ∧ renameFml ρ ψ
renameFml ρ (φ ∨ ψ)          = renameFml ρ φ ∨ renameFml ρ ψ
renameFml ρ (All φ)          = All (renameFml (liftRen ρ) φ)
renameFml ρ (Ex φ)           = Ex (renameFml (liftRen ρ) φ)

wkFml : ∀ {ℓ} {Σ : Signature {ℓ}} {n} → Fml Σ n → Fml Σ (suc n)
wkFml = renameFml wkRen

wkCtx : ∀ {ℓ} {Σ : Signature {ℓ}} {n} → Ctx Σ n → Ctx Σ (suc n)
wkCtx = map wkFml

-- Open a binder by substituting the bound variable with an existing term.

openRen : ∀ {n} → Term n → Ren (suc n) n
openRen t fzero    = t
openRen t (fsuc i) = i

inst : ∀ {ℓ} {Σ : Signature {ℓ}} {n} → Term n → Fml Σ (suc n) → Fml Σ n
inst t = renameFml (openRen t)
