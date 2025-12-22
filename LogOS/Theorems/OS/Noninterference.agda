{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.OS.Noninterference where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (_↔_)

open import LogOS.Base.Signature
open import LogOS.Minimal.Adapter
open import LogOS.Minimal.Con
open import LogOS.Minimal.Truth as Truth
open import LogOS.Kernel
open import LogOS.Kernel.Endo

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
    module CP = ConPoset CP
    module HT = Truth.HomotypicalTruth Sig Q HWorld

  ObsEq : CP.Con → CP.Con → Set ℓ
  ObsEq c d = ∀ (w : Cosp) →
    (HT.HLayer.Sat_H HTruth w c) ↔ (HT.HLayer.Sat_H HTruth w d)

  CodeObsEq : Code → Code → Set ℓ
  CodeObsEq γ δ = ObsEq (decode γ) (decode δ)

  ObsEq-refl : ∀ c → ObsEq c c
  ObsEq-refl c w = record { to = λ x → x ; from = λ x → x }

  ObsEq-sym : ∀ {c d} → ObsEq c d → ObsEq d c
  ObsEq-sym eq w = record { to = _↔_.from (eq w) ; from = _↔_.to (eq w) }

  ObsEq-trans : ∀ {c d e} → ObsEq c d → ObsEq d e → ObsEq c e
  ObsEq-trans cd de w =
    record
      { to   = λ sc → _↔_.to (de w) (_↔_.to (cd w) sc)
      ; from = λ se → _↔_.from (cd w) (_↔_.from (de w) se)
      }

  record NonInterferingEndo (f : Endo K) : Set (lsuc ℓ) where
    field
      preserves : ∀ {c d} → ObsEq c d → ObsEq (Endo.fn f c) (Endo.fn f d)

  -- Composition of noninterfering steps is noninterfering.

  noninterfering-comp
    : ∀ {f g}
    → NonInterferingEndo f → NonInterferingEndo g
    → NonInterferingEndo (g ∘E f)
  noninterfering-comp {f} {g} nf ng .NonInterferingEndo.preserves eq =
    NonInterferingEndo.preserves ng (NonInterferingEndo.preserves nf eq)
