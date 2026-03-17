{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.DisplayedThin2Cat.SuccessorStage where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- One generated layer above a base thin 2-category.
--
-- This packages the recurring LT move:
-- - choose a displayed layer over a base thin 2-category,
-- - totalise it,
-- - and keep the inherited-refinement projections explicit.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; _⊑_; _≈_)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (Thin2Functor)
open import LogOS.LT.DisplayedThin2Cat.Core using (DisplayedThin2Cat; Ob; HomD)
import LogOS.LT.DisplayedThin2Cat.Totalisation as Total

record SuccessorStage
  {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom : Level}
  (C : Thin2Cat ℓObj ℓHomCon ℓHomRel)
  : Set (lsuc (ℓObj ⊔ ℓHomCon ⊔ ℓHomRel ⊔ ℓDObj ⊔ ℓDHom)) where
  constructor mkSuccessorStage
  field
    Displayed : DisplayedThin2Cat C ℓDObj ℓDHom

  Next : Thin2Cat _ _ _
  Next = Total.DecoratedThin2Cat Displayed

  forget : Thin2Functor Next C
  forget = Total.forgetDecorated Displayed

  baseObj : Thin2Cat.Obj Next → Thin2Cat.Obj C
  baseObj = Total.base {D = Displayed}

  dispObj : (X : Thin2Cat.Obj Next) → Ob Displayed (baseObj X)
  dispObj = Total.disp {D = Displayed}

  baseHom
    : ∀ {X Y : Thin2Cat.Obj Next}
    → Con (Thin2Cat.Hom Next X Y)
    → Con (Thin2Cat.Hom C (baseObj X) (baseObj Y))
  baseHom = Total.baseHom {D = Displayed}

  dispHom
    : ∀ {X Y : Thin2Cat.Obj Next}
    → (f : Con (Thin2Cat.Hom Next X Y))
    → HomD Displayed (baseHom f) (dispObj X) (dispObj Y)
  dispHom = Total.dispHom {D = Displayed}

open SuccessorStage public using (Displayed; Next; forget; baseObj; dispObj; baseHom; dispHom)

total⊑→base⊑
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (S : SuccessorStage {ℓDObj = ℓDObj} {ℓDHom = ℓDHom} C)
    {X Y : Thin2Cat.Obj (Next S)}
    {f g : Con (Thin2Cat.Hom (Next S) X Y)}
  → _⊑_ (Thin2Cat.Hom (Next S) X Y) f g
  → _⊑_ (Thin2Cat.Hom C (baseObj S X) (baseObj S Y))
      (baseHom S f)
      (baseHom S g)
total⊑→base⊑ S {X = X} {Y = Y} {f = f} {g = g} =
  Total.total⊑→base⊑ (Displayed S) {X = X} {Y = Y} {f = f} {g = g}

base⊑→total⊑
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (S : SuccessorStage {ℓDObj = ℓDObj} {ℓDHom = ℓDHom} C)
    {X Y : Thin2Cat.Obj (Next S)}
    {f g : Con (Thin2Cat.Hom (Next S) X Y)}
  → _⊑_ (Thin2Cat.Hom C (baseObj S X) (baseObj S Y))
      (baseHom S f)
      (baseHom S g)
  → _⊑_ (Thin2Cat.Hom (Next S) X Y) f g
base⊑→total⊑ S {X = X} {Y = Y} {f = f} {g = g} =
  Total.base⊑→total⊑ (Displayed S) {X = X} {Y = Y} {f = f} {g = g}

total≈→base≈
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (S : SuccessorStage {ℓDObj = ℓDObj} {ℓDHom = ℓDHom} C)
    {X Y : Thin2Cat.Obj (Next S)}
    {f g : Con (Thin2Cat.Hom (Next S) X Y)}
  → _≈_ (Thin2Cat.Hom (Next S) X Y) f g
  → _≈_ (Thin2Cat.Hom C (baseObj S X) (baseObj S Y))
      (baseHom S f)
      (baseHom S g)
total≈→base≈ S {X = X} {Y = Y} {f = f} {g = g} =
  Total.total≈→base≈ (Displayed S) {X = X} {Y = Y} {f = f} {g = g}

base≈→total≈
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (S : SuccessorStage {ℓDObj = ℓDObj} {ℓDHom = ℓDHom} C)
    {X Y : Thin2Cat.Obj (Next S)}
    {f g : Con (Thin2Cat.Hom (Next S) X Y)}
  → _≈_ (Thin2Cat.Hom C (baseObj S X) (baseObj S Y))
      (baseHom S f)
      (baseHom S g)
  → _≈_ (Thin2Cat.Hom (Next S) X Y) f g
base≈→total≈ S {X = X} {Y = Y} {f = f} {g = g} =
  Total.base≈→total≈ (Displayed S) {X = X} {Y = Y} {f = f} {g = g}

baseHom≡→total≈
  : ∀ {ℓObj ℓHomCon ℓHomRel ℓDObj ℓDHom}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (S : SuccessorStage {ℓDObj = ℓDObj} {ℓDHom = ℓDHom} C)
    {X Y : Thin2Cat.Obj (Next S)}
    {f g : Con (Thin2Cat.Hom (Next S) X Y)}
  → baseHom S f ≡ baseHom S g
  → _≈_ (Thin2Cat.Hom (Next S) X Y) f g
baseHom≡→total≈ S {X = X} {Y = Y} {f = f} {g = g} =
  Total.baseHom≡→total≈ {D = Displayed S} {X = X} {Y = Y} {f = f} {g = g}
