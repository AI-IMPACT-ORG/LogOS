{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Logic.FOL.Soundness where

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_; intro; ⊥; ⊥-elim)

open import Data.Fin using (Fin)
open import Data.List using (_∷_)
open import Data.Product using (_×_; Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import LogOS.Logic.FOL.Syntax
open import LogOS.Logic.FOL.Subst
import LogOS.Logic.FOL.Semantics
open import LogOS.Logic.FOL.ND

-- Soundness of natural deduction with respect to the set-theoretic semantics.
-- This is the key “interpretation statement”: derivations preserve validity in
-- every model/structure (here: any domain + interpretation of predicate symbols).

module _ {ℓΣ ℓ : Level}
         {Σ₀ : Signature {ℓΣ}}
         (D    : Set ℓ)
         (PredI : PredSym Σ₀ → D → Set ℓ)
         (RelI  : RelSym₂ Σ₀ → D → D → Set ℓ)
         where

  open LogOS.Logic.FOL.Semantics.For D PredI RelI

  sound
    : ∀ {n} {Γ : Ctx Σ₀ n} {φ : Fml Σ₀ n}
    → Deriv Γ φ
    → (env : Env n)
    → SatCtx env Γ
    → Sat env φ
  sound (hyp i) env satΓ = satCtx-lookup i satΓ
  sound (⊥E d) env satΓ  = ⊥-elim (sound d env satΓ)

  sound (⇒I d) env satΓ =
    λ satφ → sound d env (satφ , satΓ)
  sound (⇒E d e) env satΓ =
    (sound d env satΓ) (sound e env satΓ)

  sound (∧I d e) env satΓ =
    (sound d env satΓ) , (sound e env satΓ)
  sound (∧E₁ d) env satΓ =
    let p = sound d env satΓ in fst p
  sound (∧E₂ d) env satΓ =
    let p = sound d env satΓ in snd p

  sound (∨I₁ d) env satΓ =
    inj₁ (sound d env satΓ)
  sound (∨I₂ d) env satΓ =
    inj₂ (sound d env satΓ)
  sound (∨E d dφ dψ) env satΓ with sound d env satΓ
  ... | inj₁ satφ = sound dφ env (satφ , satΓ)
  ... | inj₂ satψ = sound dψ env (satψ , satΓ)

  sound {Γ = Γ} (∀I {φ = φ} d) env satΓ =
    λ d0 → sound d (extend d0 env) (satCtx-wk env d0 Γ satΓ)
  sound (∀E {φ = φ} d t) env satΓ =
    Prop.from (sat-inst env t φ) ((sound d env satΓ) (env t))

  sound (∃I {φ = φ} t d) env satΓ =
    env t , Prop.to (sat-inst env t φ) (sound d env satΓ)
  sound {Γ = Γ} (∃E {φ = φ} {ψ = ψ} d k) env satΓ with sound d env satΓ
  ... | (d0 , satφ) =
    let satWK : SatCtx (extend d0 env) (φ ∷ wkCtx Γ)
        satWK = satφ , satCtx-wk env d0 Γ satΓ
        resWK : Sat (extend d0 env) (wkFml ψ)
        resWK = sound k (extend d0 env) satWK
    in Prop.to (sat-wk env d0 ψ) resWK
