{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Kernel.LogicKernel.VacuityGuards where

-- Non-vacuity witnesses for a LogicKernel: boundary truth is neither all-true
-- nor all-false at some world, and the boundary constraint space is nontrivial.

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_)

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
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
    c₀ c₁  : Con_bnd
    c₀≢c₁  : ¬ (c₀ ≡ c₁)
    w      : Cosp
    sat₀   : Sat_H_bnd (to∂ w) c₀
    unsat₁ : ¬ (Sat_H_bnd (to∂ w) c₁)
