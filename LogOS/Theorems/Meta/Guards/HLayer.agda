{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Theorems.Meta.Guards.HLayer where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.World as Worlds
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth

open import LogOS.Theorems.Meta.Guards

module For {ℓ : Level} (Sig : LogOSSignature ℓ) (Q : QAdapter ℓ) (WH : Worlds.WorldH Sig Q) where

  module HT = Truth.HomotypicalTruth Sig Q WH
  open HT

  nonVacuousSatH
    : ∀ {BB : BulkBoundary ℓ}
      {H : HLayer BB}
    → NonVacuousHLayer H
    → NonVacuousSat
        (LogOSSignature.Cosp Sig)
        (BulkBoundary.Con_bnd BB)
        (HLayer.Sat_H H)
  nonVacuousSatH NV =
    record
      { w = NonVacuousHLayer.w NV
      ; c₀ = NonVacuousHLayer.c₀ NV
      ; c₁ = NonVacuousHLayer.c₁ NV
      ; sat₀ = NonVacuousHLayer.sat₀ NV
      ; unsat₁ = NonVacuousHLayer.unsat₁ NV
      }
