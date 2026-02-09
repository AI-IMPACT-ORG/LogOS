{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.OS.Noninterference where

open import LogOS.Prelude
open import LogOS.Syntax.Prop as Prop using (_↔_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Kernel.Endo
import LogOS.Minimal.View as View

-- OS-style noninterference, phrased in a LogOS-native way: two boundary
-- constraints (or two codes via decode) are indistinguishable to all H-tier
-- observers (all `w : Cosp`), and a “noninterfering step” preserves that
-- indistinguishability.
--
-- This is intentionally a theorem *schema*: preservation requires an explicit
-- hypothesis about the step, since Sat_H is model-defined.

module _ {ℓ : Level} {Sig : LogOSSignature ℓ} {Q : QAdapter ℓ}
         (K : Kernel Sig Q) where
  open LogOSSignature Sig using (Cosp)
  open Kernel K
  private
    CP = BulkBoundary.bnd BB
    module CP = ConPreorder CP
    module HT = Truth.HomotypicalTruth Sig Q HWorld

  ObsEq : CP.Con → CP.Con → Set ℓ
  ObsEq = Prop.ObsEqOn (HT.HLayer.Sat_H HTruth)

  -- Canonical notion: observational mutual refinement (`≈`-shaped).
  Obs≈ : CP.Con → CP.Con → Set ℓ
  Obs≈ = View.Obs≈ (HT.HLayer.Sat_H HTruth)

  ObsEq↔Obs≈ : ∀ {c d} → ObsEq c d ↔ Obs≈ c d
  ObsEq↔Obs≈ {c} {d} =
    View.ObsEqOn↔Obs≈ (HT.HLayer.Sat_H HTruth) {x = c} {y = d}

  CodeObsEq : Code → Code → Set ℓ
  CodeObsEq γ δ = ObsEq (decode γ) (decode δ)

  CodeObs≈ : Code → Code → Set ℓ
  CodeObs≈ γ δ = Obs≈ (decode γ) (decode δ)

  ObsEq-refl : ∀ c → ObsEq c c
  ObsEq-refl c w = Prop.↔-refl

  ObsEq-sym : ∀ {c d} → ObsEq c d → ObsEq d c
  ObsEq-sym eq w = Prop.↔-sym (eq w)

  ObsEq-trans : ∀ {c d e} → ObsEq c d → ObsEq d e → ObsEq c e
  ObsEq-trans cd de w = Prop.↔-trans (cd w) (de w)

  record NonInterferingEndo (f : Endo K) : Set (lsuc ℓ) where
    field
      preserves : ∀ {c d} → ObsEq c d → ObsEq (Endo.fn f c) (Endo.fn f d)

  record NonInterferingEndo≈ (f : Endo K) : Set (lsuc ℓ) where
    field
      preserves≈ : ∀ {c d} → Obs≈ c d → Obs≈ (Endo.fn f c) (Endo.fn f d)

  noninterfering→noninterfering≈
    : ∀ {f} → NonInterferingEndo f → NonInterferingEndo≈ f
  noninterfering→noninterfering≈ {f} nf .NonInterferingEndo≈.preserves≈ {c} {d} cd≈ =
    Prop._↔_.to (ObsEq↔Obs≈ {c = Endo.fn f c} {d = Endo.fn f d})
      (NonInterferingEndo.preserves nf (Prop._↔_.from (ObsEq↔Obs≈ {c = c} {d = d}) cd≈))

  noninterfering≈→noninterfering
    : ∀ {f} → NonInterferingEndo≈ f → NonInterferingEndo f
  noninterfering≈→noninterfering {f} nf .NonInterferingEndo.preserves {c} {d} cdEq =
    Prop._↔_.from (ObsEq↔Obs≈ {c = Endo.fn f c} {d = Endo.fn f d})
      (NonInterferingEndo≈.preserves≈ nf (Prop._↔_.to (ObsEq↔Obs≈ {c = c} {d = d}) cdEq))

  -- Composition of noninterfering steps is noninterfering.

  noninterfering-comp
    : ∀ {f g}
    → NonInterferingEndo f → NonInterferingEndo g
    → NonInterferingEndo (g ∘E f)
  noninterfering-comp {f} {g} nf ng .NonInterferingEndo.preserves eq =
    NonInterferingEndo.preserves ng (NonInterferingEndo.preserves nf eq)

  noninterfering≈-comp
    : ∀ {f g}
    → NonInterferingEndo≈ f → NonInterferingEndo≈ g
    → NonInterferingEndo≈ (g ∘E f)
  noninterfering≈-comp {f} {g} nf ng .NonInterferingEndo≈.preserves≈ eq =
    NonInterferingEndo≈.preserves≈ ng (NonInterferingEndo≈.preserves≈ nf eq)
