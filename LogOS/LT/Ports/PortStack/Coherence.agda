{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.LT.Ports.PortStack.Coherence where

-- SpecRef: v5.8 (synchronized with docs/Core/Spec/LogicalTransformers.lagda.md)

-- Refinement transport for stacked ports.
--
-- These laws expose the inherited totalisation coherence explicitly for stacks:
-- comparisons in the stacked world transport to the base and back again.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (Con; _⊑_; _≈_)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.DisplayedThin2Cat.SuccessorStage using
  ( SuccessorStage
  ; mkSuccessorStage
  ; total⊑→base⊑
  ; base⊑→total⊑
  ; total≈→base≈
  ; base≈→total≈
  )
open import LogOS.LT.Ports.PortStack.Raw using
  ( PortStack
  ; StackDisplayed
  ; StackCat
  ; baseObj
  ; baseHom
  )

stackStage
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
  → (S : PortStack C)
  → SuccessorStage C
stackStage S = mkSuccessorStage (StackDisplayed S)

stack⊑→base⊑
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (S : PortStack C)
    {X Y : Thin2Cat.Obj (StackCat S)}
    {f g : Con (Thin2Cat.Hom (StackCat S) X Y)}
  → _⊑_ (Thin2Cat.Hom (StackCat S) X Y) f g
  → _⊑_ (Thin2Cat.Hom C (baseObj {C = C} {S = S} X) (baseObj {C = C} {S = S} Y))
      (baseHom {C = C} {S = S} f)
      (baseHom {C = C} {S = S} g)
stack⊑→base⊑ S {X = X} {Y = Y} {f = f} {g = g} =
  total⊑→base⊑ (stackStage S) {X = X} {Y = Y} {f = f} {g = g}

base⊑→stack⊑
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (S : PortStack C)
    {X Y : Thin2Cat.Obj (StackCat S)}
    {f g : Con (Thin2Cat.Hom (StackCat S) X Y)}
  → _⊑_ (Thin2Cat.Hom C (baseObj {C = C} {S = S} X) (baseObj {C = C} {S = S} Y))
      (baseHom {C = C} {S = S} f)
      (baseHom {C = C} {S = S} g)
  → _⊑_ (Thin2Cat.Hom (StackCat S) X Y) f g
base⊑→stack⊑ S {X = X} {Y = Y} {f = f} {g = g} =
  base⊑→total⊑ (stackStage S) {X = X} {Y = Y} {f = f} {g = g}

stack≈→base≈
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (S : PortStack C)
    {X Y : Thin2Cat.Obj (StackCat S)}
    {f g : Con (Thin2Cat.Hom (StackCat S) X Y)}
  → _≈_ (Thin2Cat.Hom (StackCat S) X Y) f g
  → _≈_ (Thin2Cat.Hom C (baseObj {C = C} {S = S} X) (baseObj {C = C} {S = S} Y))
      (baseHom {C = C} {S = S} f)
      (baseHom {C = C} {S = S} g)
stack≈→base≈ S {X = X} {Y = Y} {f = f} {g = g} =
  total≈→base≈ (stackStage S) {X = X} {Y = Y} {f = f} {g = g}

base≈→stack≈
  : ∀ {ℓObj ℓHomCon ℓHomRel}
    {C : Thin2Cat ℓObj ℓHomCon ℓHomRel}
    (S : PortStack C)
    {X Y : Thin2Cat.Obj (StackCat S)}
    {f g : Con (Thin2Cat.Hom (StackCat S) X Y)}
  → _≈_ (Thin2Cat.Hom C (baseObj {C = C} {S = S} X) (baseObj {C = C} {S = S} Y))
      (baseHom {C = C} {S = S} f)
      (baseHom {C = C} {S = S} g)
  → _≈_ (Thin2Cat.Hom (StackCat S) X Y) f g
base≈→stack≈ S {X = X} {Y = Y} {f = f} {g = g} =
  base≈→total≈ (stackStage S) {X = X} {Y = Y} {f = f} {g = g}
