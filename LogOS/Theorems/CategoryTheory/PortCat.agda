{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
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

open import LogOS.Ports.Semantic.PresentationCore using (PresentationC; PresentationHom; PresentationHom-respects-ObsEq)
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Boundary.IO
open import LogOS.Boundary.Port
import LogOS.Ports.Semantic.Interoperability as Interop

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
  PortHom : Port → Port → Set (lsuc (ℓCtx ⊔ ℓSat ⊔ ℓForm))
  PortHom = PresentationHom

  open PresentationHom public

  -- Equality on morphisms: indistinguishable by *target* satisfaction.
  infix 4 _≈⇒_
  _≈⇒_ : ∀ {A B} → PortHom A B → PortHom A B → Set (ℓCtx ⊔ ℓSat ⊔ ℓForm)
  _≈⇒_ {B = B} f g =
    ∀ p φ → SatF B p (map f φ) ↔ SatF B p (map g φ)

  -- (Helper) A satisfaction-preserving map respects observational equality.
  respects-ObsEq
    : ∀ {A B}
    → (h : PortHom A B)
    → ∀ {φ ψ}
    → ObsEqF A φ ψ
    → ObsEqF B (map h φ) (map h ψ)
  respects-ObsEq h = PresentationHom-respects-ObsEq h

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

module Boundary
  {ℓ : Level}
  {ℓForm : Level}
  {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
  {W : Worlds.WorldH Sig Q}
  {BB : BulkBoundary ℓ}
  {H : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB}
  (B : BoundaryIO Sig Q W BB H)
  where

  private
    Port : Set (lsuc (ℓ ⊔ ℓForm))
    Port = BoundaryPort {ℓForm = ℓForm} Sig Q W BB H B

  -- Category wrapper: boundary ports + adapters, equality via presentations.
  record PortCat : Set (lsuc (lsuc (ℓ ⊔ ℓForm))) where
    infixr 9 _∘_
    field
      Hom    : (A B : Port) → Set (lsuc (ℓ ⊔ ℓForm))
      _∘_    : ∀ {A B C} → Hom B C → Hom A B → Hom A C
      id     : ∀ {A} → Hom A A

      eqHom  : ∀ {A B} → Hom A B → Hom A B → Set (ℓ ⊔ ℓForm)
      reflH  : ∀ {A B} (f : Hom A B) → eqHom f f
      symH   : ∀ {A B} {f g : Hom A B} → eqHom f g → eqHom g f
      transH : ∀ {A B} {f g h : Hom A B} → eqHom f g → eqHom g h → eqHom f h
      cong-∘ : ∀ {A B C} {f f' : Hom A B} {g g' : Hom B C}
             → eqHom f f' → eqHom g g' → eqHom (g ∘ f) (g' ∘ f')

  PortCat-instance : PortCat
  PortCat-instance =
    record
      { Hom = λ P₁ P₂ → Interop.PortAdapter B P₁ P₂
      ; _∘_ = λ {P₁} {P₂} {P₃} g f → Interop.composeAdapter B P₁ P₂ P₃ f g
      ; id  = λ {A} → Interop.idAdapter B A
      ; eqHom = λ {P₁} {P₂} f g →
          ∀ p φ →
            BoundaryPort.SatF P₂ p (Interop.PortAdapter.map f φ)
              ↔ BoundaryPort.SatF P₂ p (Interop.PortAdapter.map g φ)
      ; reflH = λ {P₁} {P₂} f _ _ → Prop.↔-refl
      ; symH = λ {P₁} {P₂} {f} {g} eq p φ → Prop.↔-sym (eq p φ)
      ; transH = λ {P₁} {P₂} {f} {g} {h} eq₁ eq₂ p φ →
          Prop.↔-trans (eq₁ p φ) (eq₂ p φ)
      ; cong-∘ = λ {P₁} {P₂} {P₃} {f} {f'} {g} {g'} eqf eqg p φ →
          let
            stepB
              : BoundaryPort.SatF P₃ p (Interop.PortAdapter.map g (Interop.PortAdapter.map f φ))
                  ↔ BoundaryPort.SatF P₃ p (Interop.PortAdapter.map g' (Interop.PortAdapter.map f φ))
            stepB = eqg p (Interop.PortAdapter.map f φ)

            stepA
              : BoundaryPort.SatF P₃ p (Interop.PortAdapter.map g' (Interop.PortAdapter.map f φ))
                  ↔ BoundaryPort.SatF P₃ p (Interop.PortAdapter.map g' (Interop.PortAdapter.map f' φ))
            stepA =
              Prop.↔-trans
                (Prop.↔-sym (Interop.PortAdapter.preserves-Sat g' p (Interop.PortAdapter.map f φ)))
                (Prop.↔-trans (eqf p φ) (Interop.PortAdapter.preserves-Sat g' p (Interop.PortAdapter.map f' φ)))
          in
          Prop.↔-trans stepB stepA
      }
