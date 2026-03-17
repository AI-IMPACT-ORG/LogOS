{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Architecture.Apex where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Generic apex packaging over one equator thin 2-category.
--
-- This is packaging only:
-- no new axioms, no new semantic layer, and no equality-first collapse.
-- An apex is just another thin 2-category together with a forgetful functor
-- back to the shared equator.
--
-- Equality bookkeeping for the standard constructors lives in the explicit
-- `LogOS.LT.Architecture.Definitional` quarantine module.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; _≈_)
open import LogOS.LT.Thin2Cat using (Thin2Cat; PullbackThin2Cat)
open import LogOS.LT.Thin2Functor using
  ( Thin2Functor
  ; mapObj
  ; mapHom
  ; id-pres
  ; comp-pres
  ; forgetPullbackThin2Functor
  )
open import LogOS.LT.DisplayedThin2Cat using
  ( DisplayedThin2Cat
  ; DecoratedThin2Cat
  ; forgetDecorated
  )

record ApexOver {ℓObj ℓHomCon ℓHomRel : Level}
  (E : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  : Setω where
  field
    ℓObjA : Level
    ℓHomConA : Level
    ℓHomRelA : Level

    Apex : Thin2Cat ℓObjA ℓHomConA ℓHomRelA
    forget : Thin2Functor Apex E

open ApexOver public

pullbackApexOver
  : ∀ {ℓObj' ℓObj ℓHomCon ℓHomRel : Level}
    {E : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → (Obj' : Set ℓObj')
  → (F : Obj' → Thin2Cat.Obj E)
  → ApexOver E
pullbackApexOver
  {ℓObj' = ℓObj'}
  {ℓHomCon = ℓHomCon}
  {ℓHomRel = ℓHomRel}
  {E = E}
  Obj'
  F
  =
  record
    { ℓObjA = ℓObj'
    ; ℓHomConA = ℓHomCon
    ; ℓHomRelA = ℓHomRel
    ; Apex = PullbackThin2Cat {C = E} Obj' F
    ; forget = forgetPullbackThin2Functor {C = E} Obj' F
    }

displayedApexOver
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom : Level}
    {E : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → (D : DisplayedThin2Cat E ℓDObj ℓDHom)
  → ApexOver E
displayedApexOver
  {ℓObj = ℓObj}
  {ℓHomCon = ℓHomCon}
  {ℓHomRel = ℓHomRel}
  {ℓDObj = ℓDObj}
  {ℓDHom = ℓDHom}
  {E = E}
  D
  =
  record
    { ℓObjA = ℓObj ⊔ ℓDObj
    ; ℓHomConA = ℓHomCon ⊔ ℓDHom
    ; ℓHomRelA = ℓHomRel
    ; Apex = DecoratedThin2Cat D
    ; forget = forgetDecorated D
    }

forget-id≈
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {E : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (A : ApexOver E)
    {X}
  → _≈_
      (Thin2Cat.Hom E
        (mapObj (forget A) X)
        (mapObj (forget A) X))
      (mapHom (forget A) (Thin2Cat.id (Apex A) {A = X}))
      (Thin2Cat.id E {A = mapObj (forget A) X})
forget-id≈ A {X} = id-pres (forget A) {A = X}

forget-comp≈
  : ∀ {ℓObj ℓHomCon ℓHomRel : Level}
    {E : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (A : ApexOver E)
    {X Y Z}
    (f : Con (Thin2Cat.Hom (Apex A) Y Z))
    (g : Con (Thin2Cat.Hom (Apex A) X Y))
  → _≈_
      (Thin2Cat.Hom E
        (mapObj (forget A) X)
        (mapObj (forget A) Z))
      (mapHom (forget A) (Thin2Cat._∘_ (Apex A) f g))
      (Thin2Cat._∘_ E
        (mapHom (forget A) f)
        (mapHom (forget A) g))
forget-comp≈ A {X} {Y} {Z} =
  comp-pres (forget A) {A = X} {B = Y} {C₀ = Z}
