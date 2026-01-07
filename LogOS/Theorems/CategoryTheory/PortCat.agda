{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.CategoryTheory.PortCat where

-- A tiny category wrapper for semantic presentations (“ports”).
--
-- This packages the interoperability story in category-shaped form:
-- - objects: presentations of a satisfaction relation (`PresentationC`)
-- - morphisms: satisfaction-preserving translations (sound+complete)
-- - morphism equality: indistinguishable by target satisfaction (`≈⇒`)
--
-- Notes:
-- - To keep the core universe-polymorphic but lightweight, we package a category
--   at a *fixed* formula universe level `ℓForm`. (Different levels can be handled
--   by choosing a larger `ℓForm` and `Lift`ing external syntax if needed.)
-- - No new axioms are introduced: all equalities are observational (`↔`), not `≡`.

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Ports.Semantic.InterlinguaCore using (PresentationC)

module For
  {ℓCtx ℓCon ℓSat ℓForm : Level}
  {Ctx : Set ℓCtx}
  {Con : Set ℓCon}
  (SatC : Ctx → Con → Set ℓSat)
  where

  -- Objects: presentations of `SatC` in a fixed formula universe.
  Port : Set (lsuc (ℓCtx ⊔ ℓCon ⊔ ℓSat ⊔ ℓForm))
  Port = PresentationC {ℓForm = ℓForm} Ctx Con SatC

  -- Bring the presentation projections into scope (as functions of a presentation).
  open PresentationC using (Form; SatF; ObsEqF)

  -- Morphisms: satisfaction-preserving translations.
  record PortHom (A B : Port) : Set (lsuc (ℓCtx ⊔ ℓSat ⊔ ℓForm)) where
    field
      map : Form A → Form B
      sem : ∀ p φ → SatF A p φ ↔ SatF B p (map φ)

  open PortHom public

  -- Equality on morphisms: indistinguishable by *target* satisfaction.
  infix 4 _≈⇒_
  _≈⇒_ : ∀ {A B} → PortHom A B → PortHom A B → Set (ℓCtx ⊔ ℓSat ⊔ ℓForm)
  _≈⇒_ {B = B} f g =
    ∀ p φ → SatF B p (map f φ) ↔ SatF B p (map g φ)

  -- (Helper) A satisfaction-preserving map respects observational equivalence.
  respects-ObsEq
    : ∀ {A B}
    → (h : PortHom A B)
    → ∀ {φ ψ}
    → ObsEqF A φ ψ
    → ObsEqF B (map h φ) (map h ψ)
  respects-ObsEq {A} {B} h {φ} {ψ} eq p =
    Prop.↔-trans
      (Prop.↔-sym (sem h p φ))
      (Prop.↔-trans (eq p) (sem h p ψ))

  idPH : ∀ {A} → PortHom A A
  idPH =
    record
      { map = λ x → x
      ; sem = λ _ _ → Prop.↔-refl
      }

  infixr 9 _∘PH_
  _∘PH_ : ∀ {A B C} → PortHom B C → PortHom A B → PortHom A C
  g ∘PH f =
    record
      { map = λ φ → map g (map f φ)
      ; sem = λ p φ → Prop.↔-trans (sem f p φ) (sem g p (map f φ))
      }

  -- Equality laws.
  refl≈⇒ : ∀ {A B} (f : PortHom A B) → f ≈⇒ f
  refl≈⇒ f _ _ = Prop.↔-refl

  sym≈⇒ : ∀ {A B} {f g : PortHom A B} → f ≈⇒ g → g ≈⇒ f
  sym≈⇒ e p φ = Prop.↔-sym (e p φ)

  trans≈⇒ : ∀ {A B} {f g h : PortHom A B} → f ≈⇒ g → g ≈⇒ h → f ≈⇒ h
  trans≈⇒ e₁ e₂ p φ = Prop.↔-trans (e₁ p φ) (e₂ p φ)

  cong-∘≈⇒
    : ∀ {A B C}
      {f f' : PortHom A B}
      {g g' : PortHom B C}
    → f ≈⇒ f'
    → g ≈⇒ g'
    → (g ∘PH f) ≈⇒ (g' ∘PH f')
  cong-∘≈⇒ {A} {B} {C} {f} {f'} {g} {g'} eqf eqg p φ =
    let
      -- First change `g` to `g'` at the same intermediate formula.
      step₁
        : SatF C p (map g (map f φ))
            ↔
          SatF C p (map g' (map f φ))
      step₁ = eqg p (map f φ)

      -- Then change the intermediate formula using that `g'` respects ObsEq on `B`.
      eqf' : ObsEqF B (map f φ) (map f' φ)
      eqf' q = eqf q φ

      step₂
        : SatF C p (map g' (map f φ))
            ↔
          SatF C p (map g' (map f' φ))
      step₂ = respects-ObsEq g' eqf' p
    in
    Prop.↔-trans step₁ step₂

  -- Package as a small “Ho-category”: equality is `≈⇒`.
  --
  -- Like `KernelCat`, the object type is fixed: presentations of a satisfaction
  -- relation. This keeps the packaging lightweight (no higher-universe `Obj` field).
  record PortCat : Set (lsuc (lsuc (ℓCtx ⊔ ℓCon ⊔ ℓSat ⊔ ℓForm))) where
    infixr 9 _∘_
    field
      Hom    : (A B : Port) → Set (lsuc (ℓCtx ⊔ ℓSat ⊔ ℓForm))
      _∘_    : ∀ {A B C} → Hom B C → Hom A B → Hom A C
      id     : ∀ {A} → Hom A A

      eqHom  : ∀ {A B} → Hom A B → Hom A B → Set (ℓCtx ⊔ ℓSat ⊔ ℓForm)
      reflH  : ∀ {A B} (f : Hom A B) → eqHom f f
      symH   : ∀ {A B} {f g : Hom A B} → eqHom f g → eqHom g f
      transH : ∀ {A B} {f g h : Hom A B} → eqHom f g → eqHom g h → eqHom f h
      cong-∘ : ∀ {A B C} {f f' : Hom A B} {g g' : Hom B C}
             → eqHom f f' → eqHom g g' → eqHom (g ∘ f) (g' ∘ f')

  PortCat-instance : PortCat
  PortCat-instance =
    record
      { Hom    = PortHom
      ; _∘_    = _∘PH_
      ; id     = idPH
      ; eqHom  = _≈⇒_
      ; reflH  = refl≈⇒
      ; symH   = λ {A} {B} {f} {g} e p φ → Prop.↔-sym (e p φ)
      ; transH = λ {A} {B} {f} {g} {h} e₁ e₂ p φ → Prop.↔-trans (e₁ p φ) (e₂ p φ)
      ; cong-∘ = λ {A} {B} {C} {f} {f'} {g} {g'} eqf eqg →
          cong-∘≈⇒ {A = A} {B = B} {C = C} {f = f} {f' = f'} {g = g} {g' = g'} eqf eqg
      }
