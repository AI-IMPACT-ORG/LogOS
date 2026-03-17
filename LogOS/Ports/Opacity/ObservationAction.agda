{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Ports.Opacity.ObservationAction where

-- Observation actions on a thin 2-category and their induced factorisations.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; Con; MonoMap; _⊑_; _≈_)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.View using (idView; pullbackView)
open import LogOS.LT.View.Factorisation using (FactorisesThrough; mapFactorisation)

record ObservationAction
  {ℓObj ℓHomCon ℓHomRel ℓObsCon ℓObsRel : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel ⊔ ℓObsCon ⊔ ℓObsRel)) where
  field
    Obs : Thin2Cat.Obj C → ConPreorder ℓObsCon ℓObsRel
    act : ∀ {A B} → Con (Thin2Cat.Hom C A B) → Con (Obs A) → Con (Obs B)
    act-mono : ∀ {A B} (h : Con (Thin2Cat.Hom C A B)) → MonoMap (Obs A) (Obs B) (act h)
    act-hom-mono
      : ∀ {A B}
        {h k : Con (Thin2Cat.Hom C A B)}
      → _⊑_ (Thin2Cat.Hom C A B) h k
      → ∀ x
      → _⊑_ (Obs B) (act h x) (act k x)

    act-id≈
      : ∀ {A} (x : Con (Obs A))
      → _≈_ (Obs A) (act (Thin2Cat.id C {A}) x) x

    act-comp≈
      : ∀ {A B D}
        (f : Con (Thin2Cat.Hom C A B))
        (g : Con (Thin2Cat.Hom C B D))
        (x : Con (Obs A))
      → _≈_ (Obs D)
          (act (Thin2Cat._∘_ C g f) x)
          (act g (act f x))

open ObservationAction public

record ProcessObservation
  {ℓObj ℓHomCon ℓHomRel ℓObsCon ℓObsRel : Level}
  {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  {A B : Thin2Cat.Obj C}
  (h : Con (Thin2Cat.Hom C A B))
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel ⊔ ℓObsCon ⊔ ℓObsRel)) where
  field
    ObsSrc : ConPreorder ℓObsCon ℓObsRel
    ObsTgt : ConPreorder ℓObsCon ℓObsRel
    act : Con ObsSrc → Con ObsTgt
    act-mono : MonoMap ObsSrc ObsTgt act

open ProcessObservation public

processFactorisation
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓObsCon ℓObsRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → (Obs : ObservationAction {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} C)
  → ∀ {A B}
  → (h : Con (Thin2Cat.Hom C A B))
  → FactorisesThrough
      (idView (ObservationAction.Obs Obs A))
      (pullbackView (act Obs h) (idView (ObservationAction.Obs Obs B)))
processFactorisation Obs h =
  mapFactorisation (act Obs h) (act-mono Obs h)

processFactorisationAt
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓObsCon ℓObsRel : Level}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    {A B : Thin2Cat.Obj C}
    {h : Con (Thin2Cat.Hom C A B)}
  → (Obs : ProcessObservation {ℓObsCon = ℓObsCon} {ℓObsRel = ℓObsRel} {C = C} {A = A} {B = B} h)
  → FactorisesThrough
      (idView (ObsSrc Obs))
      (pullbackView (act Obs) (idView (ObsTgt Obs)))
processFactorisationAt Obs =
  mapFactorisation (act Obs) (act-mono Obs)
