{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Logic.FOL.Semantics where

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_; intro; ⊥)

open import Data.Fin using (Fin; fzero; fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import LogOS.Logic.FOL.Syntax
open import LogOS.Logic.FOL.Subst

-- Semantics for relational FOL, parameterised by a domain and an interpretation
-- of unary and binary symbols.

module For {ℓΣ ℓ : Level}
           {Σ₀ : Signature {ℓΣ}}
           (D    : Set ℓ)
           (PredI : PredSym Σ₀ → D → Set ℓ)
           (RelI  : RelSym₂ Σ₀ → D → D → Set ℓ)
           where

  Env : ℕ → Set ℓ
  Env n = Fin n → D

  extend : ∀ {n} → D → Env n → Env (suc n)
  extend d ρ fzero    = d
  extend d ρ (fsuc i) = ρ i

  Sat : ∀ {n} → Env n → Fml Σ₀ n → Set ℓ
  Sat ρ ⊥ᶠ           = ⊥ {ℓ}
  Sat ρ (pred p x)    = PredI p (ρ x)
  Sat ρ (rel₂ r x y)  = RelI r (ρ x) (ρ y)
  Sat ρ (φ ⇒ ψ)       = Sat ρ φ → Sat ρ ψ
  Sat ρ (φ ∧ ψ)       = Sat ρ φ × Sat ρ ψ
  Sat ρ (φ ∨ ψ)       = Sat ρ φ ⊎ Sat ρ ψ
  Sat ρ (All φ)       = ∀ d → Sat (extend d ρ) φ
  Sat ρ (Ex  φ)       = Σ D (λ d → Sat (extend d ρ) φ)

  -- Pointwise equality of environments (avoids assuming function extensionality).

  EnvEq : ∀ {n} → Env n → Env n → Set ℓ
  EnvEq ρ₁ ρ₂ = ∀ i → ρ₁ i ≡ ρ₂ i

  extendEq : ∀ {n} {ρ₁ ρ₂ : Env n} → EnvEq ρ₁ ρ₂ → ∀ d → EnvEq (extend d ρ₁) (extend d ρ₂)
  extendEq eq d fzero    = refl
  extendEq eq d (fsuc i) = eq i

  subst₂
    : ∀ {ℓA ℓB ℓP}
      {A : Set ℓA} {B : Set ℓB}
      (P : A → B → Set ℓP)
      {a₁ a₂ : A} {b₁ b₂ : B}
    → a₁ ≡ a₂ → b₁ ≡ b₂ → P a₁ b₁ → P a₂ b₂
  subst₂ P refl refl p = p

  -- Satisfaction respects pointwise environment equality.

  sat-envEq : ∀ {n} {ρ₁ ρ₂ : Env n} → EnvEq ρ₁ ρ₂ → (φ : Fml Σ₀ n) → Sat ρ₁ φ ↔ Sat ρ₂ φ
  sat-envEq eq ⊥ᶠ = intro (λ x → x) (λ x → x)
  sat-envEq eq (pred p x) =
    intro
      (subst (PredI p) (eq x))
      (subst (PredI p) (sym (eq x)))
  sat-envEq eq (rel₂ r x y) =
    intro
      (subst₂ (RelI r) (eq x) (eq y))
      (subst₂ (RelI r) (sym (eq x)) (sym (eq y)))
  sat-envEq eq (φ ⇒ ψ) with sat-envEq eq φ | sat-envEq eq ψ
  ... | intro φ→ φ← | intro ψ→ ψ← =
    intro
      (λ f a → ψ→ (f (φ← a)))
      (λ g a → ψ← (g (φ→ a)))
  sat-envEq eq (φ ∧ ψ) with sat-envEq eq φ | sat-envEq eq ψ
  ... | intro φ→ φ← | intro ψ→ ψ← =
    intro
      (λ where (a , b) → (φ→ a , ψ→ b))
      (λ where (a , b) → (φ← a , ψ← b))
  sat-envEq eq (φ ∨ ψ) with sat-envEq eq φ | sat-envEq eq ψ
  ... | intro φ→ φ← | intro ψ→ ψ← =
    intro
      (λ where
        (inj₁ a) → inj₁ (φ→ a)
        (inj₂ b) → inj₂ (ψ→ b))
      (λ where
        (inj₁ a) → inj₁ (φ← a)
        (inj₂ b) → inj₂ (ψ← b))
  sat-envEq eq (All φ) =
    intro
      (λ h d → Prop.to (sat-envEq (extendEq eq d) φ) (h d))
      (λ h d → Prop.from (sat-envEq (extendEq eq d) φ) (h d))
  sat-envEq eq (Ex φ) =
    intro
      (λ where (d , p) → d , Prop.to (sat-envEq (extendEq eq d) φ) p)
      (λ where (d , p) → d , Prop.from (sat-envEq (extendEq eq d) φ) p)

  -- Environment action for renamings.

  renEnv : ∀ {m n} → Ren m n → Env n → Env m
  renEnv ρ env i = env (ρ i)

  renEnv-liftRen-extend
    : ∀ {m n} (ρ : Ren m n) (env : Env n) (d : D)
    → EnvEq (renEnv (liftRen ρ) (extend d env))
            (extend d (renEnv ρ env))
  renEnv-liftRen-extend ρ env d fzero    = refl
  renEnv-liftRen-extend ρ env d (fsuc i) = refl

  -- Renaming lemma for satisfaction (no function extensionality needed).

  sat-rename : ∀ {m n} (ρ : Ren m n) (env : Env n) (φ : Fml Σ₀ m)
             → Sat env (renameFml ρ φ) ↔ Sat (renEnv ρ env) φ
  sat-rename ρ env ⊥ᶠ = intro (λ x → x) (λ x → x)
  sat-rename ρ env (pred p x) = intro (λ x → x) (λ x → x)
  sat-rename ρ env (rel₂ r x y) = intro (λ x → x) (λ x → x)
  sat-rename ρ env (φ ⇒ ψ) with sat-rename ρ env φ | sat-rename ρ env ψ
  ... | intro φ→ φ← | intro ψ→ ψ← =
    intro
      (λ f a → ψ→ (f (φ← a)))
      (λ g a → ψ← (g (φ→ a)))
  sat-rename ρ env (φ ∧ ψ) with sat-rename ρ env φ | sat-rename ρ env ψ
  ... | intro φ→ φ← | intro ψ→ ψ← =
    intro
      (λ where (a , b) → (φ→ a , ψ→ b))
      (λ where (a , b) → (φ← a , ψ← b))
  sat-rename ρ env (φ ∨ ψ) with sat-rename ρ env φ | sat-rename ρ env ψ
  ... | intro φ→ φ← | intro ψ→ ψ← =
    intro
      (λ where
        (inj₁ a) → inj₁ (φ→ a)
        (inj₂ b) → inj₂ (ψ→ b))
      (λ where
        (inj₁ a) → inj₁ (φ← a)
        (inj₂ b) → inj₂ (ψ← b))
  sat-rename ρ env (All φ) =
    intro
      (λ h d →
        let ih   = sat-rename (liftRen ρ) (extend d env) φ
            coh  = sat-envEq (renEnv-liftRen-extend ρ env d) φ
        in Prop.to coh (Prop.to ih (h d)))
      (λ h d →
        let ih   = sat-rename (liftRen ρ) (extend d env) φ
            coh  = sat-envEq (renEnv-liftRen-extend ρ env d) φ
        in Prop.from ih (Prop.from coh (h d)))
  sat-rename ρ env (Ex φ) =
    intro
      (λ where
        (d , p) →
          let ih  = sat-rename (liftRen ρ) (extend d env) φ
              coh = sat-envEq (renEnv-liftRen-extend ρ env d) φ
          in d , Prop.to coh (Prop.to ih p))
      (λ where
        (d , p) →
          let ih  = sat-rename (liftRen ρ) (extend d env) φ
              coh = sat-envEq (renEnv-liftRen-extend ρ env d) φ
          in d , Prop.from ih (Prop.from coh p))

  -- Two common corollaries used in soundness proofs.

  sat-wk : ∀ {n} (env : Env n) (d : D) (φ : Fml Σ₀ n)
         → Sat (extend d env) (wkFml φ) ↔ Sat env φ
  sat-wk env d φ =
    let ih  = sat-rename wkRen (extend d env) φ
        eq  : EnvEq (renEnv wkRen (extend d env)) env
        eq = λ _ → refl
        coh = sat-envEq eq φ
    in intro
      (λ p → Prop.to coh (Prop.to ih p))
      (λ p → Prop.from ih (Prop.from coh p))

  sat-inst : ∀ {n} (env : Env n) (t : Term n) (φ : Fml Σ₀ (suc n))
           → Sat env (inst t φ) ↔ Sat (extend (env t) env) φ
  sat-inst env t φ =
    let ih  = sat-rename (openRen t) env φ
        eq  : EnvEq (renEnv (openRen t) env) (extend (env t) env)
        eq = λ where
          fzero    → refl
          (fsuc i) → refl
        coh = sat-envEq eq φ
    in intro
      (λ p → Prop.to coh (Prop.to ih p))
      (λ p → Prop.from ih (Prop.from coh p))

  -- Context semantics (conjunction of assumptions).

  SatCtx : ∀ {n} → Env n → Ctx Σ₀ n → Set ℓ
  SatCtx env []       = ⊤
  SatCtx env (φ ∷ Γ)  = Sat env φ × SatCtx env Γ

  satCtx-lookup : ∀ {n} {env : Env n} {Γ : Ctx Σ₀ n} {φ : Fml Σ₀ n}
                → φ ∈ᶜ Γ → SatCtx env Γ → Sat env φ
  satCtx-lookup here       (p , _)   = p
  satCtx-lookup (there i)  (_ , ps)  = satCtx-lookup i ps

  satCtx-wk
    : ∀ {n} (env : Env n) (d : D) (Γ : Ctx Σ₀ n)
    → SatCtx env Γ → SatCtx (extend d env) (wkCtx Γ)
  satCtx-wk env d []       ps = tt
  satCtx-wk env d (φ ∷ Γ)  (p , ps) =
    (Prop.from (sat-wk env d φ) p) , satCtx-wk env d Γ ps
