{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Semantic.Presentation2Cat where

-- Thin 2-category of presentations (ports) over a *fixed* satisfaction system:
-- - objects: presentations `PresentationC S`,
-- - 1-cells: semantic translations `PresentationHom` (preserve+reflect Sat),
-- - 2-cells: pointwise refinement on translated meaning (implication on Sat).
--
-- This is a bookkeeping/typing device: it packages the already-present
-- satisfaction-based notion of translation into the standard Thin2Cat shape.

open import LogOS.Prelude

open import LogOS.Syntax.Prop as Prop

open import LogOS.Ports.Semantic.PresentationCore using
  ( SatSystem
  ; PresentationC
  ; PresentationHom
  ; PresentationHom-id
  ; PresentationHom-compose
  )

open import LogOS.Minimal.Con using (ConPreorder; _≈CP_)
open import LogOS.Minimal.Thin2Cat using (Thin2Cat; Thin2CatLaws)
open import LogOS.Minimal.RelPreorder as RP using (RelPreorder)
open import LogOS.Minimal.RelThin2Cat using (RelThin2Cat; RelThin2CatLaws)

module For
  {ℓCtx ℓCon ℓSat ℓForm : Level}
  {S : SatSystem {ℓCtx = ℓCtx} {ℓCon = ℓCon} {ℓSat = ℓSat}}
  where

  Obj : Set _
  Obj = PresentationC {ℓForm = ℓForm} S

  HomPreorder : Obj → Obj → ConPreorder (lsuc (lsuc (ℓCtx ⊔ ℓSat ⊔ ℓForm)))
  HomPreorder P₁ P₂ =
    let
      module P2 = PresentationC P₂
      ℓHom = lsuc (lsuc (ℓCtx ⊔ ℓSat ⊔ ℓForm))
    in
    record
      { Con = Lift ℓHom (PresentationHom P₁ P₂)
      ; _⊑_ = λ h k →
          Lift ℓHom
            (∀ p φ → P2.SatF p (PresentationHom.map (Lift.lower h) φ) → P2.SatF p (PresentationHom.map (Lift.lower k) φ))
      ; refl = λ {h} → lift (λ _ _ sat → sat)
      ; trans = λ {h} {k} {l} hk kl →
          lift (λ p φ sat → Lift.lower kl p φ (Lift.lower hk p φ sat))
      }

  id₁ : ∀ {P : Obj} → ConPreorder.Con (HomPreorder P P)
  id₁ {P} = lift (PresentationHom-id P)

  infixr 9 _∘₁_
  _∘₁_ : ∀ {A B C : Obj}
        → ConPreorder.Con (HomPreorder B C)
        → ConPreorder.Con (HomPreorder A B)
        → ConPreorder.Con (HomPreorder A C)
  _∘₁_ g f = lift (PresentationHom-compose (Lift.lower f) (Lift.lower g))

  comp-mono-l
    : ∀ {A B C : Obj}
      {f f' : ConPreorder.Con (HomPreorder B C)}
      {g : ConPreorder.Con (HomPreorder A B)}
    → ConPreorder._⊑_ (HomPreorder B C) f f'
    → ConPreorder._⊑_ (HomPreorder A C) (f ∘₁ g) (f' ∘₁ g)
  comp-mono-l {C = P₃} {g = g} f≤f' =
    let module P3 = PresentationC P₃ in
    lift (λ p φ → Lift.lower f≤f' p (PresentationHom.map (Lift.lower g) φ))

  comp-mono-r
    : ∀ {A B C : Obj}
      {f : ConPreorder.Con (HomPreorder B C)}
      {g g' : ConPreorder.Con (HomPreorder A B)}
    → ConPreorder._⊑_ (HomPreorder A B) g g'
    → ConPreorder._⊑_ (HomPreorder A C) (f ∘₁ g) (f ∘₁ g')
  comp-mono-r {B = P₂} {C = P₃} {f = f} {g = g} {g' = g'} g≤g' =
    let
      module P2 = PresentationC P₂
      module P3 = PresentationC P₃
    in
    lift (λ p φ sat →
      let
        -- Use conservativity of `f` to move the premise to the intermediate Sat,
        -- apply the 2-cell there, then move back.
        toB   : P2.SatF p (PresentationHom.map (Lift.lower g) φ)
        toB   =
          Prop._↔_.from
            (PresentationHom.sem (Lift.lower f) p (PresentationHom.map (Lift.lower g) φ))
            sat

        toB'  : P2.SatF p (PresentationHom.map (Lift.lower g') φ)
        toB'  = Lift.lower g≤g' p φ toB

        backC : P3.SatF p (PresentationHom.map (Lift.lower f) (PresentationHom.map (Lift.lower g') φ))
        backC =
          Prop._↔_.to
            (PresentationHom.sem (Lift.lower f) p (PresentationHom.map (Lift.lower g') φ))
            toB'
      in backC)

  PresentationThin2Cat
    : Thin2Cat (lsuc (ℓCtx ⊔ ℓCon ⊔ ℓSat ⊔ ℓForm))
               (lsuc (lsuc (ℓCtx ⊔ ℓSat ⊔ ℓForm)))
  PresentationThin2Cat =
    record
      { Obj = Obj
      ; Hom = HomPreorder
      ; id  = id₁
      ; _∘_ = _∘₁_
      ; comp-mono-l = λ {A} {B} {C} {f} {f'} {g} le →
          comp-mono-l {A = A} {B = B} {C = C} {f = f} {f' = f'} {g = g} le
      ; comp-mono-r = λ {A} {B} {C} {f} {g} {g'} le →
          comp-mono-r {A = A} {B = B} {C = C} {f = f} {g = g} {g' = g'} le
      }

  -- Laws hold up to mutual refinement (as usual in Thin2Cat).
  PresentationThin2CatLaws : Thin2CatLaws PresentationThin2Cat
  PresentationThin2CatLaws =
    record
      { id-left = λ _ → (lift (λ _ _ sat → sat) , lift (λ _ _ sat → sat))
      ; id-right = λ _ → (lift (λ _ _ sat → sat) , lift (λ _ _ sat → sat))
      ; assoc = λ _ _ _ → (lift (λ _ _ sat → sat) , lift (λ _ _ sat → sat))
      }

  -- RelPreorder-enriched version (no `Lift` needed).

  infix 4 _⊑PH_
  _⊑PH_ : ∀ {P₁ P₂ : Obj} → PresentationHom P₁ P₂ → PresentationHom P₁ P₂ → Set (ℓCtx ⊔ ℓSat ⊔ ℓForm)
  _⊑PH_ {P₂ = P₂} f g =
    let module P2 = PresentationC P₂ in
    ∀ p φ → P2.SatF p (PresentationHom.map f φ) → P2.SatF p (PresentationHom.map g φ)

  HomRelPreorder : Obj → Obj → RelPreorder (lsuc (ℓCtx ⊔ ℓSat ⊔ ℓForm)) (ℓCtx ⊔ ℓSat ⊔ ℓForm)
  HomRelPreorder P₁ P₂ =
    record
      { Con = PresentationHom P₁ P₂
      ; _⊑_ = _⊑PH_
      ; refl = λ {h} _ _ sat → sat
      ; trans = λ {f} {g} {h} fg gh p φ sat → gh p φ (fg p φ sat)
      }

  PresentationRelThin2Cat
    : RelThin2Cat (lsuc (ℓCtx ⊔ ℓCon ⊔ ℓSat ⊔ ℓForm))
                 (lsuc (ℓCtx ⊔ ℓSat ⊔ ℓForm))
                 (ℓCtx ⊔ ℓSat ⊔ ℓForm)
  PresentationRelThin2Cat =
    record
      { Obj = Obj
      ; Hom = HomRelPreorder
      ; id  = λ {A} → PresentationHom-id A
      ; _∘_ = λ g f → PresentationHom-compose f g
      ; comp-mono-l = λ {A} {B} {C} {f} {f'} {g} le →
          (λ p φ → le p (PresentationHom.map g φ))
      ; comp-mono-r = λ {A} {B} {C} {f} {g} {g'} le →
          let
            module PB = PresentationC B
          in
          (λ p φ sat →
            let
              toB : PB.SatF p (PresentationHom.map g φ)
              toB =
                Prop._↔_.from
                  (PresentationHom.sem f p (PresentationHom.map g φ))
                  sat

              toB' : PB.SatF p (PresentationHom.map g' φ)
              toB' = le p φ toB
            in
            Prop._↔_.to
              (PresentationHom.sem f p (PresentationHom.map g' φ))
              toB')
      }

  PresentationRelThin2CatLaws : RelThin2CatLaws PresentationRelThin2Cat
  PresentationRelThin2CatLaws =
    record
      { id-left = λ _ → ((λ _ _ sat → sat) , (λ _ _ sat → sat))
      ; id-right = λ _ → ((λ _ _ sat → sat) , (λ _ _ sat → sat))
      ; assoc = λ _ _ _ → ((λ _ _ sat → sat) , (λ _ _ sat → sat))
      }
