{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.VacuityGuards where

-- Non-vacuity witnesses for a LogicKernel: boundary truth is neither all-true
-- nor all-false at some world, and the boundary constraint space is
-- observationally nontrivial (w.r.t. boundary satisfaction).

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Boundary.Port using (_≈∂[_]_)
open import LogOS.Kernel.LogicKernel.Boundary using (boundaryIO)
import LogOS.Kernel.LogicKernel as LK

record KernelVacuityGuards
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q : QAdapter ℓ}
  (K : LK.LogicKernel Sig Q)
  : Set (lsuc (lsuc ℓ)) where
  open LK.LogicKernel K
  open LogOSSignature Sig
  open BulkBoundary BB using (Con_bnd)
  field
    w      : Cosp
    c₀ c₁  : Con_bnd
    sat₀   : Sat_H_bnd (to∂ w) c₀
    unsat₁ : ¬ (Sat_H_bnd (to∂ w) c₁)

  -- Derived: the witnesses are observationally distinguishable by boundary satisfaction.
  c₀≉c₁ : ¬ (c₀ ≈∂[ boundaryIO K ] c₁)
  c₀≉c₁ eq = unsat₁ (LogOS.Syntax.Prop.to (eq (to∂ w)) sat₀)

  -- Convenience: definitional distinctness follows from observational distinctness.
  c₀≢c₁ : ¬ (c₀ ≡ c₁)
  c₀≢c₁ eq = unsat₁ (subst (Sat_H_bnd (to∂ w)) eq sat₀)
