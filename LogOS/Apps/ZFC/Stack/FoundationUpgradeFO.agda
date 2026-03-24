{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.FoundationUpgradeFO where

-- Foundation as an explicit FO-level upgrade step.
--
-- This module is intentionally “ledger-shaped”:
-- - the ZF Foundation law in `ZFCore` is the implication/inhabitedness form,
-- - a stronger disjunctive form can be derived once a chooser is installed,
-- - assumptions are factored into independent upgrades (choice vs wf).

open import LogOS.Prelude
open import LogOS.Host.Nat using (zero; suc)
open import LogOS.Syntax.Prop using (_↔_; intro)
open import LogOS.LT.View using (μ)

import LogOS.Apps.ZFC.Proof.Syntax as Syn
import LogOS.Apps.ZFC.Stack.ProfileTower.Core as Tower
import LogOS.Apps.ZFC.Stack.ProfileTowerFO as TowerFO
import LogOS.Apps.ZFC.Stack.WellFounded as WF

module ForBase {ℓ : Level} (B : Tower.ZFStackBase {ℓ}) where
  open Tower.ZFStackBase B
  module Base = TowerFO.ForBase B

  record EmptyOrElemUpgrade : Set (lsuc ℓ) where
    field
      chooseEmptyOrElem
        : (x : SetU)
        → (x ≈ Base.zeroSet) ⊎ (Σ SetU (λ y → y ∈ x))

  record MemWellFoundedUpgrade : Set (lsuc ℓ) where
    field
      wfMem : (x : SetU) → WF.Acc _∈_ x

  record FoundationAssumptions : Set (lsuc ℓ) where
    field
      choice : EmptyOrElemUpgrade
      wf     : MemWellFoundedUpgrade

  foundationAssumptions
    : EmptyOrElemUpgrade
    → ((x : SetU) → WF.Acc _∈_ x)
    → FoundationAssumptions
  foundationAssumptions choice wfMem =
    record
      { choice = choice
      ; wf = record { wfMem = wfMem }
      }

  open EmptyOrElemUpgrade public
  open MemWellFoundedUpgrade public
  open FoundationAssumptions public

module ForBaseSep
  {ℓ : Level}
  (B : Tower.ZFStackBase {ℓ})
  (Sep : TowerFO.SeparationFOUpgrade B)
  where

  open Tower.ZFStackBase B
  open TowerFO.SeparationFOUpgrade Sep public using (SeparationFV; separationF-spec)

  module Base = TowerFO.ForBase B
  module Core = ForBase B
  open Core public using
    ( EmptyOrElemUpgrade
    ; MemWellFoundedUpgrade
    ; FoundationAssumptions
    ; foundationAssumptions
    ; chooseEmptyOrElem
    ; wfMem
    ; choice
    ; wf
    )
  -- ----------------------------------------------------------------------
  -- FO intersection via Separation (used to descend along membership).

  -- Predicate: "z ∈ param0" under Separation context (z , x , params...).
  interPred : Syn.Formula
  interPred = (Syn.var zero) Syn.∈F (Syn.var (suc (suc zero)))

  interVal : SetU → Base.Valuation
  interVal y = Base.extend y (λ _ → Base.zeroSet)

  interSet : SetU → SetU → SetU
  interSet x y = μ (SeparationFV interPred (interVal y)) x

  mem-inter↔ : ∀ x y z → (z ∈ interSet x y) ↔ ((z ∈ x) × (z ∈ y))
  mem-inter↔ x y z =
    let
      sepLaw
        : (z ∈ interSet x y)
            ↔ ((z ∈ x) × Base.evalFormula interPred (Base.extend z (Base.extend x (interVal y))))
      sepLaw = separationF-spec interPred (interVal y) x z

      -- Definitional computation of `interPred`.
      evalInter : Base.evalFormula interPred (Base.extend z (Base.extend x (interVal y))) ≡ (z ∈ y)
      evalInter = refl
    in
    intro
      (λ z∈ →
        let p = _↔_.to sepLaw z∈ in
        fst p , subst (λ Q → Q) evalInter (snd p))
      (λ p →
        _↔_.from sepLaw (fst p , subst (λ Q → Q) (sym evalInter) (snd p)))

  -- ----------------------------------------------------------------------
  -- Minimal element search (well-founded descent in the membership tree).

  -- If `x ∩ y` is empty, then no element of `x` is a member of `y`.
  interEmpty⇒min
    : ∀ {x y}
    → interSet x y ≈ Base.zeroSet
    → (∀ z → z ∈ x → ¬ (z ∈ y))
  interEmpty⇒min {x = x} {y = y} inter≈0 z z∈x z∈y =
    empty-spec z
      (fst inter≈0 z (_↔_.from (mem-inter↔ x y z) (z∈x , z∈y)))

  -- Starting from any witness `y ∈ x`, descend until `x ∩ y` is empty.
  minFrom
    : (A : FoundationAssumptions)
    → ∀ (x y : SetU)
    → y ∈ x
    → WF.Acc _∈_ y
    → Σ SetU (λ m → m ∈ x × (∀ z → z ∈ x → ¬ (z ∈ m)))
  minFrom A x y y∈x (WF.acc step)
    with chooseEmptyOrElem (choice A) (interSet x y)
  ... | inj₁ inter≈0 =
    y , (y∈x , interEmpty⇒min inter≈0)
  ... | inj₂ (z , z∈inter) =
    let
      z∈x : z ∈ x
      z∈x = fst (_↔_.to (mem-inter↔ x y z) z∈inter)

      z∈y : z ∈ y
      z∈y = snd (_↔_.to (mem-inter↔ x y z) z∈inter)
    in
    minFrom A x z z∈x (step z z∈y)

  -- ----------------------------------------------------------------------
  -- Construct the (implication-form) Foundation law as an explicit upgrade.

  foundationUpgrade : FoundationAssumptions → Tower.FoundationUpgrade B
  foundationUpgrade A =
    record
      { foundationLaws =
          record
            { foundation = foundation }
      }
    where
      foundation
        : ∀ x
        → (Σ SetU (λ y → y ∈ x))
        → Σ SetU (λ y → y ∈ x × (∀ z → z ∈ x → ¬ (z ∈ y)))
      foundation x (y , y∈x) =
        minFrom A x y y∈x (wfMem (wf A) y)

  -- ----------------------------------------------------------------------
  -- Derive the stronger disjunctive form once a chooser is installed.

  foundationDisj
    : (C : EmptyOrElemUpgrade)
    → Tower.FoundationUpgrade B
    → ∀ x
    → (x ≈ Base.zeroSet)
      ⊎ (Σ SetU (λ y → y ∈ x × (∀ z → z ∈ x → ¬ (z ∈ y))))
  foundationDisj C F x with chooseEmptyOrElem C x
  ... | inj₁ x≈0 = inj₁ x≈0
  ... | inj₂ (y , y∈x) = inj₂ (Tower.FoundationUpgrade.foundation F x (y , y∈x))

module For {ℓ : Level} (S : TowerFO.ZFStackFO₋Fnd {ℓ}) where
  module Impl =
    ForBaseSep
      (TowerFO.ZFStackFO₋Fnd.base S)
      (TowerFO.ZFStackFO₋Fnd.sep S)

  open Impl public
