{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Boundary.KernelVacuityGuards where

-- Non-vacuity witnesses for a Kernel: boundary truth is neither all-true
-- nor all-false at some world, and the boundary constraint space is
-- observationally nontrivial (w.r.t. boundary satisfaction).

open import LogOS.Prelude
import LogOS.Syntax.Prop as Prop
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth
import LogOS.Minimal.View as View
open import LogOS.Boundary.Port using (_≈∂[_]_; ObsEq∂; ObsLe∂; ObsEq∂↔Obs≈∂)
open import LogOS.Boundary.FromKernel using (boundaryIO)
import LogOS.Kernel as LK

record KernelVacuityGuards
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : LK.Kernel Sig Q)
  : Set (lsuc (lsuc ℓ)) where
  open LK.Kernel K
  open LogOSSignature Sig
  open BulkBoundary BB using (Con_bnd)

  -- Reuse the *core* H-tier notion of non-vacuity (in `LogOS.Minimal.Truth`),
  -- then transport it along `sat-coh` to obtain a boundary-satisfaction witness.
  private
    module HT = Truth.HomotypicalTruth Sig Q HWorld

  field
    nonVacuousHTruth : HT.NonVacuousHLayer HTruth

  open HT.NonVacuousHLayer nonVacuousHTruth public renaming
    ( w to w
    ; c₀ to c₀
    ; c₁ to c₁
    ; sat₀ to sat₀H
    ; unsat₁ to unsat₁H
    )

  sat₀ : Sat_H_bnd (to∂ w) c₀
  sat₀ = Prop.to (sat-coh w c₀) sat₀H

  unsat₁ : ¬ (Sat_H_bnd (to∂ w) c₁)
  unsat₁ sat = unsat₁H (Prop.from (sat-coh w c₁) sat)

  -- Derived: the witnesses are observationally distinguishable by boundary satisfaction.
  c₀≰c₁ : ¬ (ObsLe∂ (boundaryIO K) c₀ c₁)
  c₀≰c₁ le = unsat₁ (le (to∂ w) sat₀)

  c₀≉c₁ : ¬ (c₀ ≈∂[ boundaryIO K ] c₁)
  c₀≉c₁ eq = unsat₁ (View.Obs≈⇒ {Sat = Sat_H_bnd} eq (to∂ w) sat₀)

  c₀≠c₁ : ¬ (ObsEq∂ (boundaryIO K) c₀ c₁)
  c₀≠c₁ eq =
    c₀≉c₁ (Prop._↔_.to (ObsEq∂↔Obs≈∂ (boundaryIO K) {c = c₀} {d = c₁}) eq)

  -- Convenience: definitional distinctness follows from observational distinctness.
  c₀≢c₁ : ¬ (c₀ ≡ c₁)
  c₀≢c₁ eq = unsat₁ (subst (Sat_H_bnd (to∂ w)) eq sat₀)
