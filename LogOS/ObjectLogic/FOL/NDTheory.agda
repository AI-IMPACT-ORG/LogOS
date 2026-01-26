{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ObjectLogic.FOL.NDTheory where

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (⊥; ⊥-elim)

open import LogOS.Prelude.List using (List; _∷_)
open import LogOS.Prelude.Product using (_×_; Σ; _,_)
open import LogOS.Prelude.Sum using (_⊎_; inj₁; inj₂)

open import LogOS.ObjectLogic.FOL.Syntax
open import LogOS.ObjectLogic.FOL.Subst
import LogOS.ObjectLogic.FOL.Semantics as Sem

-- Natural deduction with an explicit axiom predicate.
--
-- This is the minimal “theory” upgrade needed to model schematic axiom sets
-- (e.g. Separation/Replacement) without enumerating finite instance lists.

data DerivAx
  {ℓΣ ℓAx : Level}
  {Σ₀ : Signature {ℓΣ}}
  (Ax  : ∀ {n} → Fml Σ₀ n → Set ℓAx)
  : ∀ {n} → Ctx Σ₀ n → Fml Σ₀ n → Set (ℓΣ ⊔ ℓAx) where

  hyp : ∀ {n} {Γ : Ctx Σ₀ n} {φ}
      → φ ∈ᶜ Γ
      → DerivAx Ax Γ φ

  ax  : ∀ {n} {Γ : Ctx Σ₀ n} {φ}
      → Ax φ
      → DerivAx Ax Γ φ

  ⊥E  : ∀ {n} {Γ : Ctx Σ₀ n} {φ}
      → DerivAx Ax Γ ⊥ᶠ
      → DerivAx Ax Γ φ

  ⇒I  : ∀ {n} {Γ : Ctx Σ₀ n} {φ ψ}
      → DerivAx Ax (φ ∷ Γ) ψ
      → DerivAx Ax Γ (φ ⇒ ψ)

  ⇒E  : ∀ {n} {Γ : Ctx Σ₀ n} {φ ψ}
      → DerivAx Ax Γ (φ ⇒ ψ)
      → DerivAx Ax Γ φ
      → DerivAx Ax Γ ψ

  ∧I  : ∀ {n} {Γ : Ctx Σ₀ n} {φ ψ}
      → DerivAx Ax Γ φ
      → DerivAx Ax Γ ψ
      → DerivAx Ax Γ (φ ∧ ψ)

  ∧E₁ : ∀ {n} {Γ : Ctx Σ₀ n} {φ ψ}
      → DerivAx Ax Γ (φ ∧ ψ)
      → DerivAx Ax Γ φ

  ∧E₂ : ∀ {n} {Γ : Ctx Σ₀ n} {φ ψ}
      → DerivAx Ax Γ (φ ∧ ψ)
      → DerivAx Ax Γ ψ

  ∨I₁ : ∀ {n} {Γ : Ctx Σ₀ n} {φ ψ}
      → DerivAx Ax Γ φ
      → DerivAx Ax Γ (φ ∨ ψ)

  ∨I₂ : ∀ {n} {Γ : Ctx Σ₀ n} {φ ψ}
      → DerivAx Ax Γ ψ
      → DerivAx Ax Γ (φ ∨ ψ)

  ∨E  : ∀ {n} {Γ : Ctx Σ₀ n} {φ ψ χ}
      → DerivAx Ax Γ (φ ∨ ψ)
      → DerivAx Ax (φ ∷ Γ) χ
      → DerivAx Ax (ψ ∷ Γ) χ
      → DerivAx Ax Γ χ

  ∀I  : ∀ {n} {Γ : Ctx Σ₀ n} {φ : Fml Σ₀ (suc n)}
      → DerivAx Ax (wkCtx Γ) φ
      → DerivAx Ax Γ (All φ)

  ∀E  : ∀ {n} {Γ : Ctx Σ₀ n} {φ : Fml Σ₀ (suc n)}
      → DerivAx Ax Γ (All φ)
      → (t : Term n)
      → DerivAx Ax Γ (inst t φ)

  ∃I  : ∀ {n} {Γ : Ctx Σ₀ n} {φ : Fml Σ₀ (suc n)}
      → (t : Term n)
      → DerivAx Ax Γ (inst t φ)
      → DerivAx Ax Γ (Ex φ)

  ∃E  : ∀ {n} {Γ : Ctx Σ₀ n} {φ : Fml Σ₀ (suc n)} {ψ : Fml Σ₀ n}
      → DerivAx Ax Γ (Ex φ)
      → DerivAx Ax (φ ∷ wkCtx Γ) (wkFml ψ)
      → DerivAx Ax Γ ψ

module Soundness
  {ℓΣ ℓD ℓAx : Level}
  {Σ₀ : Signature {ℓΣ}}
  (D    : Set ℓD)
  (PredI : PredSym Σ₀ → D → Set ℓD)
  (RelI  : RelSym₂ Σ₀ → D → D → Set ℓD)
  where

  open Sem.For D PredI RelI

  soundAx
    : (Ax : ∀ {n} → Fml Σ₀ n → Set ℓAx)
    → (axValid : ∀ {n} {φ : Fml Σ₀ n} → Ax φ → ∀ env → Sat env φ)
    → ∀ {n} {Γ : Ctx Σ₀ n} {φ : Fml Σ₀ n}
    → DerivAx Ax Γ φ
    → (env : Env n)
    → SatCtx env Γ
    → Sat env φ
  soundAx Ax axValid (hyp i) env satΓ = satCtx-lookup i satΓ
  soundAx Ax axValid (ax h) env satΓ = axValid h env
  soundAx Ax axValid (⊥E d) env satΓ = ⊥-elim (soundAx Ax axValid d env satΓ)

  soundAx Ax axValid (⇒I d) env satΓ =
    λ satφ → soundAx Ax axValid d env (satφ , satΓ)
  soundAx Ax axValid (⇒E d e) env satΓ =
    (soundAx Ax axValid d env satΓ) (soundAx Ax axValid e env satΓ)

  soundAx Ax axValid (∧I d e) env satΓ =
    (soundAx Ax axValid d env satΓ) , (soundAx Ax axValid e env satΓ)
  soundAx Ax axValid (∧E₁ d) env satΓ = fst (soundAx Ax axValid d env satΓ)
  soundAx Ax axValid (∧E₂ d) env satΓ = snd (soundAx Ax axValid d env satΓ)

  soundAx Ax axValid (∨I₁ d) env satΓ = inj₁ (soundAx Ax axValid d env satΓ)
  soundAx Ax axValid (∨I₂ d) env satΓ = inj₂ (soundAx Ax axValid d env satΓ)
  soundAx Ax axValid (∨E d dφ dψ) env satΓ with soundAx Ax axValid d env satΓ
  ... | inj₁ satφ = soundAx Ax axValid dφ env (satφ , satΓ)
  ... | inj₂ satψ = soundAx Ax axValid dψ env (satψ , satΓ)

  soundAx Ax axValid {Γ = Γ} (∀I {φ = φ} d) env satΓ =
    λ d0 → soundAx Ax axValid d (extend d0 env) (satCtx-wk env d0 Γ satΓ)
  soundAx Ax axValid (∀E {φ = φ} d t) env satΓ =
    Prop.from (sat-inst env t φ) ((soundAx Ax axValid d env satΓ) (env t))

  soundAx Ax axValid (∃I {φ = φ} t d) env satΓ =
    env t , Prop.to (sat-inst env t φ) (soundAx Ax axValid d env satΓ)
  soundAx Ax axValid {Γ = Γ} (∃E {φ = φ} {ψ = ψ} d k) env satΓ
    with soundAx Ax axValid d env satΓ
  ... | (d0 , satφ) =
    let
      satWK : SatCtx (extend d0 env) (φ ∷ wkCtx Γ)
      satWK = satφ , satCtx-wk env d0 Γ satΓ

      resWK : Sat (extend d0 env) (wkFml ψ)
      resWK = soundAx Ax axValid k (extend d0 env) satWK
    in
    Prop.to (sat-wk env d0 ψ) resWK
