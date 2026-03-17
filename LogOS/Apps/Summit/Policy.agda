{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Summit.Policy where

-- Summit policy layer.
--
-- This file is intentionally small: it does not introduce new theorem content.
-- It only names the two extra choices needed to read the existing capstone
-- theorems as an apps-side “summit” capstone surface:
--
-- 1. a conservative generalisation of a seed mechanisable boundary world into a
--    downstream thin logic, and
-- 2. an explicit quoted/self-reference policy on a chosen fibre of that seed.
--
-- The summit-level reading is that these are not governance-style policies.
-- They are the explicit extra witnesses needed before a downstream logic may be
-- called mechanisable in the strong apps-side sense.

open import LogOS.Prelude
open import LogOS.LT.ConPreorder using (ConPreorder; _≈_)
open import LogOS.LT.Thin2Cat using (Thin2Cat)
open import LogOS.LT.Thin2Functor using (ConservativeThin2Functor)
open import LogOS.LT.Flow using (GuardedClosure; Flow; Stable; elem)

open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.Bicategory using
  ( BicatW
  ; BicatW→TwoCellOps
  )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.TwoCellOps using
  ( TwoCellOps )
open import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.ShadowByView using
  ( ShadowByView )
import LogOS.Apps.LogicArchitecture.MetaTheory.Basis.FoundationalLogic as FoundationalLogic
import LogOS.Ports.Reification.GuardedLawvere as GuardedLawvere

record GeneralisationPolicy
  {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
  {B : BicatW ℓObj ℓHom₁ ℓHom₂}
  {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
     → TwoCellOps.Obj (BicatW→TwoCellOps B)
     → ConPreorder ℓOCon ℓORel}
  {S : ShadowByView (BicatW→TwoCellOps B) O}
  {ℓDObj ℓDHom₁ ℓDHom₂ : Level}
  (M : FoundationalLogic.MechanisableLogicWorld B O S)
  (D : Thin2Cat ℓDObj ℓDHom₁ ℓDHom₂)
  : Setω where
  private
    module M = FoundationalLogic.MechanisableLogicWorld M
  field
    generalise : ConservativeThin2Functor M.boundaryWorld D

open GeneralisationPolicy public

record ObstructionPolicy
  {ℓObj ℓHom₁ ℓHom₂ ℓOCon ℓORel : Level}
  {B : BicatW ℓObj ℓHom₁ ℓHom₂}
  {O : TwoCellOps.Obj (BicatW→TwoCellOps B)
     → TwoCellOps.Obj (BicatW→TwoCellOps B)
     → ConPreorder ℓOCon ℓORel}
  {S : ShadowByView (BicatW→TwoCellOps B) O}
  (M : FoundationalLogic.MechanisableLogicWorld B O S)
  : Setω where
  private
    module Seed = FoundationalLogic.MechanisableLogicWorld M
  field
    A₀ B₀ : TwoCellOps.Obj (BicatW→TwoCellOps B)

    guardedClosure
      : GuardedClosure
          (FoundationalLogic.BoundarySemanticsAt {B = B} {O = O} S A₀ B₀)

    Aℓ Xℓ : Level
    A : Set Aℓ
    X : Set Xℓ

    evaluator
      : GuardedLawvere.StableEvaluator
          A
          X
          (FoundationalLogic.BoundarySemanticsAt {B = B} {O = O} S A₀ B₀)
          guardedClosure

    obstructionData
      : Σ
          (Stable
             {CP = FoundationalLogic.BoundarySemanticsAt {B = B} {O = O} S A₀ B₀}
             (Flow guardedClosure)
             →
           Stable
             {CP = FoundationalLogic.BoundarySemanticsAt {B = B} {O = O} S A₀ B₀}
             (Flow guardedClosure))
          (λ α →
            ∀ p →
            ¬ _≈_
                (FoundationalLogic.BoundarySemanticsAt {B = B} {O = O} S A₀ B₀)
                (elem p)
                (elem (α p)))

open ObstructionPolicy public
