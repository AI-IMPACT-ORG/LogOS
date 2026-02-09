{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Computation.Process2Cat where

-- Thin 2-category of processes (scheme/process layer):
-- - objects: `Process Output`,
-- - 1-cells: lax process morphisms `ProcessHomLax`,
-- - 2-cells: pointwise refinement on the state translation map.
--
-- This packages the “simulation map” discipline in a way that Agda can check
-- uniformly: parallel morphisms can be compared, whiskered, and composed
-- without inventing bespoke notions each time.

open import LogOS.Prelude

open import LogOS.Minimal.Con using (ConPreorder; _≈CP_)
open import LogOS.Minimal.Thin2Cat using (Thin2Cat; Thin2CatLaws)
open import LogOS.Minimal.RelPreorder as RP using (RelPreorder)
open import LogOS.Minimal.RelThin2Cat using (RelThin2Cat; RelThin2CatLaws)

import LogOS.Computation.SchemeCategory as Cat

module For
  {ℓO ℓC ℓQ : Level}
  {Output : Set ℓO}
  where

  Obj : Set (lsuc (ℓO ⊔ ℓC ⊔ ℓQ))
  Obj = Cat.Process {ℓO} {ℓC} {ℓQ} Output

  -- Pointwise refinement between lax process morphisms (in the target preorder).
  infix 4 _⊑ProcHom_
  _⊑ProcHom_ : ∀ {P₁ P₂ : Obj} → Cat.ProcessHomLax P₁ P₂ → Cat.ProcessHomLax P₁ P₂ → Set (lsuc (ℓO ⊔ ℓC ⊔ ℓQ))
  _⊑ProcHom_ {P₂ = P₂} f g =
    Lift (lsuc (ℓO ⊔ ℓC ⊔ ℓQ))
      (∀ c → Cat.Process._⊑_ P₂ (Cat.ProcessHomLax.map f c) (Cat.ProcessHomLax.map g c))

  HomPreorder : Obj → Obj → ConPreorder (lsuc (ℓO ⊔ ℓC ⊔ ℓQ))
  HomPreorder P₁ P₂ =
    record
      { Con   = Cat.ProcessHomLax P₁ P₂
      ; _⊑_   = _⊑ProcHom_
      ; refl  = λ {f} → lift (λ _ → Cat.Process.refl P₂)
      ; trans = λ {f} {g} {h} fg gh →
          lift (λ c → Cat.Process.trans P₂ (Lift.lower fg c) (Lift.lower gh c))
      }

  id₁ : ∀ {P : Obj} → ConPreorder.Con (HomPreorder P P)
  id₁ {P} = Cat.idProcessHomLax P

  infixr 9 _∘₁_
  _∘₁_ : ∀ {P₁ P₂ P₃ : Obj}
        → ConPreorder.Con (HomPreorder P₂ P₃)
        → ConPreorder.Con (HomPreorder P₁ P₂)
        → ConPreorder.Con (HomPreorder P₁ P₃)
  _∘₁_ = Cat._∘ProcessHomLax_

  comp-mono-l
    : ∀ {A B C : Obj}
      {f f' : ConPreorder.Con (HomPreorder B C)}
      {g : ConPreorder.Con (HomPreorder A B)}
    → ConPreorder._⊑_ (HomPreorder B C) f f'
    → ConPreorder._⊑_ (HomPreorder A C) (f ∘₁ g) (f' ∘₁ g)
  comp-mono-l {f = f} {f' = f'} {g = g} f≤f' =
    lift (λ c → Lift.lower f≤f' (Cat.ProcessHomLax.map g c))

  comp-mono-r
    : ∀ {A B C : Obj}
      {f : ConPreorder.Con (HomPreorder B C)}
      {g g' : ConPreorder.Con (HomPreorder A B)}
    → ConPreorder._⊑_ (HomPreorder A B) g g'
    → ConPreorder._⊑_ (HomPreorder A C) (f ∘₁ g) (f ∘₁ g')
  comp-mono-r {f = f} {g = g} {g' = g'} g≤g' =
    lift (λ c → Cat.ProcessHomLax.mono f (Lift.lower g≤g' c))

  ProcessThin2Cat : Thin2Cat (lsuc (ℓO ⊔ ℓC ⊔ ℓQ)) (lsuc (ℓO ⊔ ℓC ⊔ ℓQ))
  ProcessThin2Cat =
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

  ProcessThin2CatLaws : Thin2CatLaws ProcessThin2Cat
  ProcessThin2CatLaws =
    record
      { id-left = λ {A} {B} f →
          ( lift (λ _ → Cat.Process.refl B)
          , lift (λ _ → Cat.Process.refl B)
          )
      ; id-right = λ {A} {B} f →
          ( lift (λ _ → Cat.Process.refl B)
          , lift (λ _ → Cat.Process.refl B)
          )
      ; assoc = λ {A} {B} {C} {D} f g h →
          ( lift (λ _ → Cat.Process.refl D)
          , lift (λ _ → Cat.Process.refl D)
          )
      }

  -- RelPreorder-enriched version (no `Lift` needed).

  infix 4 _⊑ProcHomRaw_
  _⊑ProcHomRaw_ : ∀ {P₁ P₂ : Obj} → Cat.ProcessHomLax P₁ P₂ → Cat.ProcessHomLax P₁ P₂ → Set ℓC
  _⊑ProcHomRaw_ {P₂ = P₂} f g =
    ∀ c → Cat.Process._⊑_ P₂ (Cat.ProcessHomLax.map f c) (Cat.ProcessHomLax.map g c)

  HomRelPreorder : Obj → Obj → RelPreorder (lsuc (ℓO ⊔ ℓC ⊔ ℓQ)) ℓC
  HomRelPreorder P₁ P₂ =
    record
      { Con = Cat.ProcessHomLax P₁ P₂
      ; _⊑_ = _⊑ProcHomRaw_
      ; refl = λ {f} _ → Cat.Process.refl P₂
      ; trans = λ {f} {g} {h} fg gh c → Cat.Process.trans P₂ (fg c) (gh c)
      }

  ProcessRelThin2Cat : RelThin2Cat (lsuc (ℓO ⊔ ℓC ⊔ ℓQ)) (lsuc (ℓO ⊔ ℓC ⊔ ℓQ)) ℓC
  ProcessRelThin2Cat =
    record
      { Obj = Obj
      ; Hom = HomRelPreorder
      ; id  = λ {A} → Cat.idProcessHomLax A
      ; _∘_ = Cat._∘ProcessHomLax_
      ; comp-mono-l = λ {A} {B} {C} {f} {f'} {g} le c →
          le (Cat.ProcessHomLax.map g c)
      ; comp-mono-r = λ {A} {B} {C} {f} {g} {g'} le c →
          Cat.ProcessHomLax.mono f (le c)
      }

  ProcessRelThin2CatLaws : RelThin2CatLaws ProcessRelThin2Cat
  ProcessRelThin2CatLaws =
    record
      { id-left = λ {A} {B} f →
          ((λ _ → Cat.Process.refl B) , (λ _ → Cat.Process.refl B))
      ; id-right = λ {A} {B} f →
          ((λ _ → Cat.Process.refl B) , (λ _ → Cat.Process.refl B))
      ; assoc = λ {A} {B} {C} {D} f g h →
          ((λ _ → Cat.Process.refl D) , (λ _ → Cat.Process.refl D))
      }
