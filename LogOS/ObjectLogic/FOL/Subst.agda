{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ObjectLogic.FOL.Subst where

open import LogOS.Prelude

open import LogOS.Prelude.Fin using (Fin; fzero; fsuc)
open import LogOS.Prelude.List using (List; map; []; _∷_; _++_)

open import LogOS.ObjectLogic.FOL.Syntax

-- Renamings (de Bruijn) and the induced action on terms/formulas/contexts.

Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n

-- Pointwise equality (avoids function extensionality).

RenEq : ∀ {m n} → Ren m n → Ren m n → Set
RenEq ρ σ = ∀ i → ρ i ≡ σ i

renEq-refl : ∀ {m n} {ρ : Ren m n} → RenEq ρ ρ
renEq-refl _ = refl

renEq-sym : ∀ {m n} {ρ σ : Ren m n} → RenEq ρ σ → RenEq σ ρ
renEq-sym eq i = sym (eq i)

renEq-trans : ∀ {m n} {ρ σ τ : Ren m n} → RenEq ρ σ → RenEq σ τ → RenEq ρ τ
renEq-trans eq₁ eq₂ i = trans (eq₁ i) (eq₂ i)

wkRen : ∀ {n} → Ren n (suc n)
wkRen = fsuc

liftRen : ∀ {m n} → Ren m n → Ren (suc m) (suc n)
liftRen ρ fzero    = fzero
liftRen ρ (fsuc i) = fsuc (ρ i)

renEq-liftRen : ∀ {m n} {ρ σ : Ren m n} → RenEq ρ σ → RenEq (liftRen ρ) (liftRen σ)
renEq-liftRen eq fzero    = refl
renEq-liftRen eq (fsuc i) = cong fsuc (eq i)

renComp : ∀ {m n k} → Ren m n → Ren n k → Ren m k
renComp ρ σ i = σ (ρ i)

renComp-liftRen
  : ∀ {m n k} (ρ : Ren m n) (σ : Ren n k)
  → RenEq (renComp (liftRen ρ) (liftRen σ)) (liftRen (renComp ρ σ))
renComp-liftRen ρ σ fzero    = refl
renComp-liftRen ρ σ (fsuc i) = refl

renameTerm : ∀ {m n} → Ren m n → Term m → Term n
renameTerm ρ x = ρ x

renameTerm-cong
  : ∀ {m n} {ρ σ : Ren m n} → RenEq ρ σ → (x : Term m) → renameTerm ρ x ≡ renameTerm σ x
renameTerm-cong eq x = eq x

renameFml : ∀ {ℓ} {Σ : Signature {ℓ}} {m n} → Ren m n → Fml Σ m → Fml Σ n
renameFml ρ ⊥ᶠ             = ⊥ᶠ
renameFml ρ (pred p x)       = pred p (renameTerm ρ x)
renameFml ρ (rel₂ r x y)     = rel₂ r (renameTerm ρ x) (renameTerm ρ y)
renameFml ρ (φ ⇒ ψ)          = renameFml ρ φ ⇒ renameFml ρ ψ
renameFml ρ (φ ∧ ψ)          = renameFml ρ φ ∧ renameFml ρ ψ
renameFml ρ (φ ∨ ψ)          = renameFml ρ φ ∨ renameFml ρ ψ
renameFml ρ (All φ)          = All (renameFml (liftRen ρ) φ)
renameFml ρ (Ex φ)           = Ex (renameFml (liftRen ρ) φ)

renameFml-cong
  : ∀ {ℓ} {Σ : Signature {ℓ}} {m n} {ρ σ : Ren m n}
  → RenEq ρ σ
  → (φ : Fml Σ m)
  → renameFml ρ φ ≡ renameFml σ φ
renameFml-cong eq ⊥ᶠ = refl
renameFml-cong eq (pred p x) = cong (pred p) (renameTerm-cong eq x)
renameFml-cong eq (rel₂ r x y) =
  cong₂ (rel₂ r) (renameTerm-cong eq x) (renameTerm-cong eq y)
renameFml-cong eq (φ ⇒ ψ) =
  cong₂ _⇒_ (renameFml-cong eq φ) (renameFml-cong eq ψ)
renameFml-cong eq (φ ∧ ψ) =
  cong₂ _∧_ (renameFml-cong eq φ) (renameFml-cong eq ψ)
renameFml-cong eq (φ ∨ ψ) =
  cong₂ _∨_ (renameFml-cong eq φ) (renameFml-cong eq ψ)
renameFml-cong eq (All φ) =
  cong All (renameFml-cong (renEq-liftRen eq) φ)
renameFml-cong eq (Ex φ) =
  cong Ex (renameFml-cong (renEq-liftRen eq) φ)

renameFml-comp
  : ∀ {ℓ} {Σ : Signature {ℓ}} {m n k}
  → (ρ : Ren m n) (σ : Ren n k) (φ : Fml Σ m)
  → renameFml σ (renameFml ρ φ) ≡ renameFml (renComp ρ σ) φ
renameFml-comp ρ σ ⊥ᶠ = refl
renameFml-comp ρ σ (pred p x) = refl
renameFml-comp ρ σ (rel₂ r x y) = refl
renameFml-comp ρ σ (φ ⇒ ψ) =
  cong₂ _⇒_ (renameFml-comp ρ σ φ) (renameFml-comp ρ σ ψ)
renameFml-comp ρ σ (φ ∧ ψ) =
  cong₂ _∧_ (renameFml-comp ρ σ φ) (renameFml-comp ρ σ ψ)
renameFml-comp ρ σ (φ ∨ ψ) =
  cong₂ _∨_ (renameFml-comp ρ σ φ) (renameFml-comp ρ σ ψ)
renameFml-comp ρ σ (All φ) =
  cong All
    (trans
      (renameFml-comp (liftRen ρ) (liftRen σ) φ)
      (renameFml-cong (renComp-liftRen ρ σ) φ))
renameFml-comp ρ σ (Ex φ) =
  cong Ex
    (trans
      (renameFml-comp (liftRen ρ) (liftRen σ) φ)
      (renameFml-cong (renComp-liftRen ρ σ) φ))

wkFml : ∀ {ℓ} {Σ : Signature {ℓ}} {n} → Fml Σ n → Fml Σ (suc n)
wkFml = renameFml wkRen

wkCtx : ∀ {ℓ} {Σ : Signature {ℓ}} {n} → Ctx Σ n → Ctx Σ (suc n)
wkCtx = map wkFml

wkCtx-++
  : ∀ {ℓ} {Σ : Signature {ℓ}} {n} (Δ Γ : Ctx Σ n)
  → wkCtx (Δ ++ Γ) ≡ wkCtx Δ ++ wkCtx Γ
wkCtx-++ [] Γ = refl
wkCtx-++ (φ ∷ Δ) Γ =
  cong₂ _∷_ refl (wkCtx-++ Δ Γ)

renComp-wkRen
  : ∀ {m n} (ρ : Ren m n)
  → RenEq (renComp wkRen (liftRen ρ)) (renComp ρ wkRen)
renComp-wkRen ρ i = refl

renameFml-wk
  : ∀ {ℓ} {Σ : Signature {ℓ}} {m n} (ρ : Ren m n) (φ : Fml Σ m)
  → renameFml (liftRen ρ) (wkFml φ) ≡ wkFml (renameFml ρ φ)
renameFml-wk ρ φ =
  trans
    (renameFml-comp wkRen (liftRen ρ) φ)
    (trans
      (renameFml-cong (renComp-wkRen ρ) φ)
      (sym (renameFml-comp ρ wkRen φ)))

renameCtx : ∀ {ℓ} {Σ : Signature {ℓ}} {m n} → Ren m n → Ctx Σ m → Ctx Σ n
renameCtx ρ = map (renameFml ρ)

renameCtx-wk
  : ∀ {ℓ} {Σ : Signature {ℓ}} {m n} (ρ : Ren m n) (Γ : Ctx Σ m)
  → renameCtx (liftRen ρ) (wkCtx Γ) ≡ wkCtx (renameCtx ρ Γ)
renameCtx-wk ρ [] = refl
renameCtx-wk ρ (φ ∷ Γ) =
  cong₂ _∷_ (renameFml-wk ρ φ) (renameCtx-wk ρ Γ)

-- Open a binder by substituting the bound variable with an existing term.

openRen : ∀ {n} → Term n → Ren (suc n) n
openRen t fzero    = t
openRen t (fsuc i) = i

renComp-openRen
  : ∀ {m n} (ρ : Ren m n) (t : Term m)
  → RenEq (renComp (openRen t) ρ)
          (renComp (liftRen ρ) (openRen (renameTerm ρ t)))
renComp-openRen ρ t fzero = refl
renComp-openRen ρ t (fsuc i) = refl

inst : ∀ {ℓ} {Σ : Signature {ℓ}} {n} → Term n → Fml Σ (suc n) → Fml Σ n
inst t = renameFml (openRen t)

instCtx : ∀ {ℓ} {Σ : Signature {ℓ}} {n} → Term n → Ctx Σ (suc n) → Ctx Σ n
instCtx t = map (inst t)

renameFml-inst
  : ∀ {ℓ} {Σ : Signature {ℓ}} {m n}
  → (ρ : Ren m n) (t : Term m) (φ : Fml Σ (suc m))
  → renameFml ρ (inst t φ)
    ≡ inst (renameTerm ρ t) (renameFml (liftRen ρ) φ)
renameFml-inst ρ t φ =
  trans
    (renameFml-comp (openRen t) ρ φ)
    (trans
      (renameFml-cong (renComp-openRen ρ t) φ)
      (sym (renameFml-comp (liftRen ρ) (openRen (renameTerm ρ t)) φ)))
