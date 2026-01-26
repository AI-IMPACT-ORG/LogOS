{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Safety.Meaningfulness where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; _↔_)
open import LogOS.Prelude.Product using (Σ; _,_; _×_)

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Kernel.LogicKernel using (LogicKernel)

-- Lightweight “vacuity guards” for sockets: rule out degenerate instantiations
-- where Safety/Objectives become tautological or observationally dead.
--
-- This module intentionally does *not* assert any of these as kernel axioms; it
-- only packages them as optional assumptions for downstream packs.

record SocketVacuityGuards
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (LK  : LogicKernel Sig Q)
  (Safety Objective : BulkBoundary.Con_bnd (LogicKernel.BB LK))
  : Set (lsuc ℓ) where

  open LogOSSignature Sig
  open BulkBoundary (LogicKernel.BB LK) using (Con_bnd)

  private
    Sat : ∂Cosp → Con_bnd → Set ℓ
    Sat = LogicKernel.Sat_H_bnd LK

  field
    safetySatSomewhere : Σ ∂Cosp (λ p → Sat p Safety)
    safetyNotTop       : Σ ∂Cosp (λ p → ¬ Sat p Safety)

    objectiveNontrivial
      : Σ (∂Cosp × ∂Cosp)
          (λ { (p₁ , p₂) → ¬ ((Sat p₁ Objective) ↔ (Sat p₂ Objective)) })

open SocketVacuityGuards public

