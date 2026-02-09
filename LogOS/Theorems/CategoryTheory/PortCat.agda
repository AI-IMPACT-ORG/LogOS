{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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
-- - morphism equality: mutual refinement by target satisfaction (`≈⇒`)
--
-- Notes:
-- - To keep the core universe-polymorphic but lightweight, we package a category
--   at a *fixed* formula universe level `ℓForm`. (Different levels can be handled
--   by choosing a larger `ℓForm` and `Lift`ing external syntax if needed.)
-- - No new axioms are introduced: equality is mutual refinement in an
--   observational preorder (pointwise `↔` remains available as a presentation layer).

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop

open import LogOS.Ports.Semantic.PresentationCore using
  ( PresentationC
  ; PresentationHom
  ; PresentationHom-respects-Obs≈F
  )
open import LogOS.Ports.Semantic.PresentationCore using (SatSystem)
open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.World
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Boundary.IO
open import LogOS.Boundary.Port
open import LogOS.System using (System)
import LogOS.Ports.Semantic.Interoperability as Interop

module For
  {ℓCtx ℓCon ℓSat ℓForm : Level}
  (S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat})
  where

  -- Objects: presentations of `SatC` in a fixed formula universe.
  Port : Set (lsuc (ℓCtx ⊔ ℓCon ⊔ ℓSat ⊔ ℓForm))
  Port = PresentationC {ℓForm = ℓForm} S

  -- Bring the presentation projections into scope (as functions of a presentation).
  open PresentationC using (Form; SatF; Obs≈F)

  -- Morphisms: satisfaction-preserving translations.
  PortHom : Port → Port → Set (lsuc (ℓCtx ⊔ ℓSat ⊔ ℓForm))
  PortHom = PresentationHom

  open PresentationHom public

  -- Equality on morphisms: mutual refinement in the observational preorder
  -- induced by target satisfaction.
  infix 4 _⊑⇒_ _≈⇒_

  _⊑⇒_ : ∀ {A B} → PortHom A B → PortHom A B → Set (ℓCtx ⊔ ℓSat ⊔ ℓForm)
  _⊑⇒_ {B = B} f g = ∀ p φ → SatF B p (map f φ) → SatF B p (map g φ)

  _≈⇒_ : ∀ {A B} → PortHom A B → PortHom A B → Set (ℓCtx ⊔ ℓSat ⊔ ℓForm)
  f ≈⇒ g = (f ⊑⇒ g) × (g ⊑⇒ f)

  -- Directional projections (canonical names): mutual refinement splits into the
  -- two entailment directions.
  ≈⇒⇒ : ∀ {A B} {f g : PortHom A B} → f ≈⇒ g → f ⊑⇒ g
  ≈⇒⇒ = fst

  ≈⇒⇐ : ∀ {A B} {f g : PortHom A B} → f ≈⇒ g → g ⊑⇒ f
  ≈⇒⇐ = snd

  -- Presentation alias: pointwise satisfaction equivalence (`↔`).
  ObsEq⇒ : ∀ {A B} → PortHom A B → PortHom A B → Set (ℓCtx ⊔ ℓSat ⊔ ℓForm)
  ObsEq⇒ {B = B} f g = ∀ p φ → SatF B p (map f φ) ↔ SatF B p (map g φ)

  ObsEq⇒↔≈⇒ : ∀ {A B} {f g : PortHom A B} → ObsEq⇒ f g ↔ (f ≈⇒ g)
  ObsEq⇒↔≈⇒ {f} {g} =
    Prop.intro
      (λ eq →
        ( (λ p φ sat → Prop._↔_.to (eq p φ) sat)
        , (λ p φ sat → Prop._↔_.from (eq p φ) sat)
        ))
      (λ (fg , gf) p φ → Prop.intro (fg p φ) (gf p φ))

  -- (Helper) A satisfaction-preserving map respects mutual refinement.
  respects-Obs≈
    : ∀ {A B}
    → (h : PortHom A B)
    → ∀ {φ ψ}
    → Obs≈F A φ ψ
    → Obs≈F B (map h φ) (map h ψ)
  respects-Obs≈ h = PresentationHom-respects-Obs≈F h

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
  refl≈⇒ f = ((λ _ _ sat → sat) , (λ _ _ sat → sat))

  sym≈⇒ : ∀ {A B} {f g : PortHom A B} → f ≈⇒ g → g ≈⇒ f
  sym≈⇒ (fg , gf) = (gf , fg)

  trans≈⇒ : ∀ {A B} {f g h : PortHom A B} → f ≈⇒ g → g ≈⇒ h → f ≈⇒ h
  trans≈⇒ (fg , gf) (gh , hg) =
    ( (λ p φ sat → gh p φ (fg p φ sat))
    , (λ p φ sat → gf p φ (hg p φ sat))
    )

  cong-∘≈⇒
    : ∀ {A B C}
      {f f' : PortHom A B}
      {g g' : PortHom B C}
    → f ≈⇒ f'
    → g ≈⇒ g'
    → (g ∘PH f) ≈⇒ (g' ∘PH f')
  cong-∘≈⇒ {A} {B} {C} {f} {f'} {g} {g'} eqf eqg =
    ( (λ p φ sat →
        let
          -- First change `g` to `g'` at the same intermediate formula.
          step₁ : SatF C p (map g' (map f φ))
          step₁ = ≈⇒⇒ {A = B} {B = C} {f = g} {g = g'} eqg p (map f φ) sat

          -- Then change the intermediate formula using that `g'` respects mutual refinement on `B`.
          eqf≈ : Obs≈F B (map f φ) (map f' φ)
          eqf≈ =
            ( (λ q s → ≈⇒⇒ {A = A} {B = B} {f = f} {g = f'} eqf q φ s)
            , (λ q s → ≈⇒⇐ {A = A} {B = B} {f = f} {g = f'} eqf q φ s)
            )

          step₂≈ : Obs≈F C (map g' (map f φ)) (map g' (map f' φ))
          step₂≈ = respects-Obs≈ g' eqf≈

          step₂ : SatF C p (map g' (map f' φ))
          step₂ =
            let (step₂⇒ , _) = step₂≈
            in step₂⇒ p step₁
        in
        step₂)
    , (λ p φ sat →
        let
          step₁ : SatF C p (map g (map f' φ))
          step₁ = ≈⇒⇐ {A = B} {B = C} {f = g} {g = g'} eqg p (map f' φ) sat

          eqf≈ : Obs≈F B (map f φ) (map f' φ)
          eqf≈ =
            ( (λ q s → ≈⇒⇒ {A = A} {B = B} {f = f} {g = f'} eqf q φ s)
            , (λ q s → ≈⇒⇐ {A = A} {B = B} {f = f} {g = f'} eqf q φ s)
            )

          step₂≈ : Obs≈F C (map g (map f φ)) (map g (map f' φ))
          step₂≈ = respects-Obs≈ g eqf≈

          step₂ : SatF C p (map g (map f φ))
          step₂ =
            let (_ , step₂⇐) = step₂≈
            in step₂⇐ p step₁
        in
        step₂)
    )

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
      ; symH   = λ {A} {B} {f} {g} e → sym≈⇒ {A = A} {B = B} {f = f} {g = g} e
      ; transH =
          λ {A} {B} {f} {g} {h} e₁ e₂ →
            trans≈⇒ {A = A} {B = B} {f = f} {g = g} {h = h} e₁ e₂
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

module BoundarySystem
  {ℓ : Level}
  {ℓForm : Level}
  (S : System {ℓ = ℓ})
  where

  open System S

  -- System-first wrapper: instantiate the boundary port category at `S.B`.
  open Boundary {ℓ = ℓ} {ℓForm = ℓForm} {Sig = Sig} {Q = Q} {W = W} {BB = BB} {H = H} B public
