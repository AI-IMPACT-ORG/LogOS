{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.ObjectLogic.FOL.ND where

open import LogOS.Prelude

open import LogOS.Prelude.Fin using (Fin)
open import LogOS.Prelude.List using (List; []; _∷_; map; _++_)

open import LogOS.ObjectLogic.FOL.Syntax
open import LogOS.ObjectLogic.FOL.Subst

-- Natural deduction for relational FOL (intuitionistic).
-- Contexts are lists; membership is `∈ᶜ` from `Syntax`.

data Deriv {ℓ : Level}
           {Σ₀ : Signature {ℓ}}
           {n  : ℕ}
           (Γ  : Ctx Σ₀ n)
           : Fml Σ₀ n → Set ℓ where

  hyp : ∀ {φ} → φ ∈ᶜ Γ → Deriv Γ φ

  ⊥E  : ∀ {φ} → Deriv Γ ⊥ᶠ → Deriv Γ φ

  ⇒I  : ∀ {φ ψ} → Deriv (φ ∷ Γ) ψ → Deriv Γ (φ ⇒ ψ)
  ⇒E  : ∀ {φ ψ} → Deriv Γ (φ ⇒ ψ) → Deriv Γ φ → Deriv Γ ψ

  ∧I  : ∀ {φ ψ} → Deriv Γ φ → Deriv Γ ψ → Deriv Γ (φ ∧ ψ)
  ∧E₁ : ∀ {φ ψ} → Deriv Γ (φ ∧ ψ) → Deriv Γ φ
  ∧E₂ : ∀ {φ ψ} → Deriv Γ (φ ∧ ψ) → Deriv Γ ψ

  ∨I₁ : ∀ {φ ψ} → Deriv Γ φ → Deriv Γ (φ ∨ ψ)
  ∨I₂ : ∀ {φ ψ} → Deriv Γ ψ → Deriv Γ (φ ∨ ψ)
  ∨E  : ∀ {φ ψ χ}
       → Deriv Γ (φ ∨ ψ)
       → Deriv (φ ∷ Γ) χ
       → Deriv (ψ ∷ Γ) χ
       → Deriv Γ χ

  ∀I  : ∀ {φ : Fml Σ₀ (suc n)} → Deriv (wkCtx Γ) φ → Deriv Γ (All φ)
  ∀E  : ∀ {φ : Fml Σ₀ (suc n)} → Deriv Γ (All φ) → (t : Term n) → Deriv Γ (inst t φ)

  ∃I  : ∀ {φ : Fml Σ₀ (suc n)} → (t : Term n) → Deriv Γ (inst t φ) → Deriv Γ (Ex φ)
  ∃E  : ∀ {φ : Fml Σ₀ (suc n)} {ψ : Fml Σ₀ n}
       → Deriv Γ (Ex φ)
       → Deriv (φ ∷ wkCtx Γ) (wkFml ψ)
       → Deriv Γ ψ

-- Context and renaming utilities --------------------------------------------

map-∈ᶜ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {f : A → B} {x} {xs}
       → x ∈ᶜ xs
       → f x ∈ᶜ map f xs
map-∈ᶜ here = here
map-∈ᶜ (there i) = there (map-∈ᶜ i)

consMap
  : ∀ {ℓ} {Σ₀ : Signature {ℓ}} {n} {Γ Δ : Ctx Σ₀ n} {φ : Fml Σ₀ n}
  → (∀ {ψ} → ψ ∈ᶜ Γ → ψ ∈ᶜ Δ)
  → (∀ {ψ} → ψ ∈ᶜ (φ ∷ Γ) → ψ ∈ᶜ (φ ∷ Δ))
consMap f here = here
consMap f (there i) = there (f i)

wkMap
  : ∀ {ℓ} {Σ₀ : Signature {ℓ}} {n} {Γ Δ : Ctx Σ₀ n}
  → (∀ {ψ} → ψ ∈ᶜ Γ → ψ ∈ᶜ Δ)
  → (∀ {ψ} → ψ ∈ᶜ wkCtx Γ → ψ ∈ᶜ wkCtx Δ)
wkMap {Γ = []} f ()
wkMap {Γ = φ ∷ Γ} f here = map-∈ᶜ (f here)
wkMap {Γ = φ ∷ Γ} f (there i) =
  wkMap {Γ = Γ} (λ {ψ} j → f (there j)) i

mapDeriv
  : ∀ {ℓ} {Σ₀ : Signature {ℓ}} {n} {Γ Δ : Ctx Σ₀ n} {φ : Fml Σ₀ n}
  → (∀ {ψ} → ψ ∈ᶜ Γ → ψ ∈ᶜ Δ)
  → Deriv Γ φ
  → Deriv Δ φ
mapDeriv f (hyp i) = hyp (f i)
mapDeriv f (⊥E d) = ⊥E (mapDeriv f d)
mapDeriv f (⇒I d) = ⇒I (mapDeriv (consMap f) d)
mapDeriv f (⇒E d e) = ⇒E (mapDeriv f d) (mapDeriv f e)
mapDeriv f (∧I d e) = ∧I (mapDeriv f d) (mapDeriv f e)
mapDeriv f (∧E₁ d) = ∧E₁ (mapDeriv f d)
mapDeriv f (∧E₂ d) = ∧E₂ (mapDeriv f d)
mapDeriv f (∨I₁ d) = ∨I₁ (mapDeriv f d)
mapDeriv f (∨I₂ d) = ∨I₂ (mapDeriv f d)
mapDeriv f (∨E d dφ dψ) =
  ∨E (mapDeriv f d)
     (mapDeriv (consMap f) dφ)
     (mapDeriv (consMap f) dψ)
mapDeriv f (∀I d) = ∀I (mapDeriv (wkMap f) d)
mapDeriv f (∀E d t) = ∀E (mapDeriv f d) t
mapDeriv f (∃I t d) = ∃I t (mapDeriv f d)
mapDeriv f (∃E d k) =
  ∃E (mapDeriv f d)
     (mapDeriv (consMap (wkMap f)) k)

-- Renaming / substitution for derivations -----------------------------------

rename-deriv
  : ∀ {ℓ} {Σ₀ : Signature {ℓ}} {m n}
  → (ρ : Ren m n)
  → {Γ : Ctx Σ₀ m} {φ : Fml Σ₀ m}
  → Deriv Γ φ
  → Deriv (renameCtx ρ Γ) (renameFml ρ φ)
rename-deriv ρ (hyp i) = hyp (map-∈ᶜ i)
rename-deriv ρ (⊥E d) = ⊥E (rename-deriv ρ d)
rename-deriv ρ (⇒I d) = ⇒I (rename-deriv ρ d)
rename-deriv ρ (⇒E d e) = ⇒E (rename-deriv ρ d) (rename-deriv ρ e)
rename-deriv ρ (∧I d e) = ∧I (rename-deriv ρ d) (rename-deriv ρ e)
rename-deriv ρ (∧E₁ d) = ∧E₁ (rename-deriv ρ d)
rename-deriv ρ (∧E₂ d) = ∧E₂ (rename-deriv ρ d)
rename-deriv ρ (∨I₁ d) = ∨I₁ (rename-deriv ρ d)
rename-deriv ρ (∨I₂ d) = ∨I₂ (rename-deriv ρ d)
rename-deriv ρ (∨E d dφ dψ) =
  ∨E (rename-deriv ρ d)
     (rename-deriv ρ dφ)
     (rename-deriv ρ dψ)
rename-deriv ρ {Γ = Γ} (∀I d) =
  let
    d' = rename-deriv (liftRen ρ) d
  in
  ∀I (subst (λ Γ' → Deriv Γ' _)
            (renameCtx-wk ρ Γ)
            d')
rename-deriv ρ {Γ = Γ} (∀E {φ = φ} d t) =
  subst
    (Deriv (renameCtx ρ Γ))
    (sym (renameFml-inst ρ t φ))
    (∀E (rename-deriv ρ d) (renameTerm ρ t))
rename-deriv ρ {Γ = Γ} (∃I {φ = φ} t d) =
  ∃I (renameTerm ρ t)
     (subst
       (Deriv (renameCtx ρ Γ))
       (renameFml-inst ρ t φ)
       (rename-deriv ρ d))
rename-deriv ρ {Γ = Γ} (∃E {φ = φ} {ψ = ψ} d k) =
  let
    k' = rename-deriv (liftRen ρ) k
    k'' =
      subst
        (λ Γ' → Deriv Γ' (renameFml (liftRen ρ) (wkFml ψ)))
        (cong (λ xs → renameFml (liftRen ρ) φ ∷ xs) (renameCtx-wk ρ Γ))
        k'
    k''' =
      subst
        (Deriv (renameFml (liftRen ρ) φ ∷ wkCtx (renameCtx ρ Γ)))
        (renameFml-wk ρ ψ)
        k''
  in
  ∃E (rename-deriv ρ d)
     k'''

wkDeriv
  : ∀ {ℓ} {Σ₀ : Signature {ℓ}} {n} {Γ : Ctx Σ₀ n} {φ : Fml Σ₀ n}
  → Deriv Γ φ
  → Deriv (wkCtx Γ) (wkFml φ)
wkDeriv = rename-deriv wkRen

inst-deriv
  : ∀ {ℓ} {Σ₀ : Signature {ℓ}} {n} {Γ : Ctx Σ₀ (suc n)} {φ : Fml Σ₀ (suc n)}
  → (t : Term n)
  → Deriv Γ φ
  → Deriv (instCtx t Γ) (inst t φ)
inst-deriv t = rename-deriv (openRen t)

-- Structural admissibility ---------------------------------------------------

weakening
  : ∀ {ℓ} {Σ₀ : Signature {ℓ}} {n}
  → {Γ : Ctx Σ₀ n} {φ ψ : Fml Σ₀ n}
  → Deriv Γ φ
  → Deriv (ψ ∷ Γ) φ
weakening = mapDeriv (λ i → there i)

exchange
  : ∀ {ℓ} {Σ₀ : Signature {ℓ}} {n}
  → {Γ : Ctx Σ₀ n} {φ ψ χ : Fml Σ₀ n}
  → Deriv (φ ∷ ψ ∷ Γ) χ
  → Deriv (ψ ∷ φ ∷ Γ) χ
exchange = mapDeriv swap where
  swap : ∀ {ℓ} {Σ₀ : Signature {ℓ}} {n} {Γ : Ctx Σ₀ n} {φ ψ χ : Fml Σ₀ n}
       → χ ∈ᶜ (φ ∷ ψ ∷ Γ)
       → χ ∈ᶜ (ψ ∷ φ ∷ Γ)
  swap here = there here
  swap (there here) = here
  swap (there (there i)) = there (there i)

contraction
  : ∀ {ℓ} {Σ₀ : Signature {ℓ}} {n}
  → {Γ : Ctx Σ₀ n} {φ ψ : Fml Σ₀ n}
  → Deriv (φ ∷ φ ∷ Γ) ψ
  → Deriv (φ ∷ Γ) ψ
contraction = mapDeriv contract where
  contract : ∀ {ℓ} {Σ₀ : Signature {ℓ}} {n} {Γ : Ctx Σ₀ n} {φ ψ : Fml Σ₀ n}
           → ψ ∈ᶜ (φ ∷ φ ∷ Γ)
           → ψ ∈ᶜ (φ ∷ Γ)
  contract here = here
  contract (there here) = here
  contract (there (there i)) = there i

cutHyp
  : ∀ {ℓ} {Σ₀ : Signature {ℓ}} {n}
  → {Γ : Ctx Σ₀ n} {φ ψ : Fml Σ₀ n}
  → (Δ : Ctx Σ₀ n)
  → Deriv Γ φ
  → ψ ∈ᶜ (Δ ++ (φ ∷ Γ))
  → Deriv (Δ ++ Γ) ψ
cutHyp [] d₁ here = d₁
cutHyp [] d₁ (there i) = hyp i
cutHyp (δ ∷ Δ) d₁ here = hyp here
cutHyp (δ ∷ Δ) d₁ (there i) = weakening (cutHyp Δ d₁ i)

cutWith
  : ∀ {ℓ} {Σ₀ : Signature {ℓ}} {n}
  → {Γ : Ctx Σ₀ n} {φ ψ : Fml Σ₀ n}
  → (Δ : Ctx Σ₀ n)
  → Deriv Γ φ
  → Deriv (Δ ++ (φ ∷ Γ)) ψ
  → Deriv (Δ ++ Γ) ψ
cutWith Δ d₁ (hyp i) = cutHyp Δ d₁ i
cutWith Δ d₁ (⊥E d) = ⊥E (cutWith Δ d₁ d)
cutWith Δ d₁ (⇒I {φ = θ} d) = ⇒I (cutWith (θ ∷ Δ) d₁ d)
cutWith Δ d₁ (⇒E d e) = ⇒E (cutWith Δ d₁ d) (cutWith Δ d₁ e)
cutWith Δ d₁ (∧I d e) = ∧I (cutWith Δ d₁ d) (cutWith Δ d₁ e)
cutWith Δ d₁ (∧E₁ d) = ∧E₁ (cutWith Δ d₁ d)
cutWith Δ d₁ (∧E₂ d) = ∧E₂ (cutWith Δ d₁ d)
cutWith Δ d₁ (∨I₁ d) = ∨I₁ (cutWith Δ d₁ d)
cutWith Δ d₁ (∨I₂ d) = ∨I₂ (cutWith Δ d₁ d)
cutWith Δ d₁ (∨E {φ = φ₁} {ψ = ψ₁} d dφ dψ) =
  ∨E (cutWith Δ d₁ d)
     (cutWith (φ₁ ∷ Δ) d₁ dφ)
     (cutWith (ψ₁ ∷ Δ) d₁ dψ)
cutWith {Γ = Γ} {φ = φ} Δ d₁ (∀I d)
  rewrite wkCtx-++ Δ (φ ∷ Γ)
  = let
      d' = cutWith {Γ = wkCtx Γ} (wkCtx Δ) (wkDeriv d₁) d
      d'' = subst (λ Γ' → Deriv Γ' _) (sym (wkCtx-++ Δ Γ)) d'
    in
    ∀I d''
cutWith Δ d₁ (∀E d t) = ∀E (cutWith Δ d₁ d) t
cutWith Δ d₁ (∃I t d) = ∃I t (cutWith Δ d₁ d)
cutWith {Γ = Γ} {φ = φ} Δ d₁ (∃E {φ = χ} d k)
  rewrite wkCtx-++ Δ (φ ∷ Γ)
  = let
      k' = cutWith {Γ = wkCtx Γ} (χ ∷ wkCtx Δ) (wkDeriv d₁) k
      k'' =
        subst
          (λ Γ' → Deriv (χ ∷ Γ') _)
          (sym (wkCtx-++ Δ Γ))
          k'
    in
    ∃E (cutWith Δ d₁ d)
       k''

cut
  : ∀ {ℓ} {Σ₀ : Signature {ℓ}} {n}
  → {Γ : Ctx Σ₀ n} {φ ψ : Fml Σ₀ n}
  → Deriv Γ φ
  → Deriv (φ ∷ Γ) ψ
  → Deriv Γ ψ
cut d₁ d₂ = cutWith [] d₁ d₂
