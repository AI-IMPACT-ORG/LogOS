{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Safety.Meaningfulness where

open import LogOS.Prelude
open import LogOS.Syntax.Prop using (¬_; _↔_)
open import LogOS.Prelude using (Σ; _,_; _×_)

open import LogOS.Base.Signature using (LogOSSignature; module LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Kernel using (Kernel)
open import LogOS.Theorems.Meta.Guards using (NonEmptyPred; NotTopPred)

-- Lightweight “vacuity guards” for sockets: rule out degenerate instantiations
-- where Safety/Objectives become tautological or observationally dead.
--
-- This module intentionally does *not* assert any of these as kernel axioms; it
-- only packages them as optional assumptions for downstream packs.

record SocketVacuityGuards
  {ℓ : Level}
  {Sig : LogOSSignature ℓ}
  {Q   : QAdapter ℓ}
  (LK  : Kernel Sig Q)
  (Safety Objective : BulkBoundary.Con_bnd (Kernel.BB LK))
  : Set (lsuc ℓ) where

  open LogOSSignature Sig
  open BulkBoundary (Kernel.BB LK) using (Con_bnd)

  private
    Sat : ∂Cosp → Con_bnd → Set ℓ
    Sat = Kernel.Sat_H_bnd LK

  field
    safetySatSomewhere : NonEmptyPred ∂Cosp (λ p → Sat p Safety)
    safetyNotTop       : NotTopPred ∂Cosp (λ p → Sat p Safety)

    objectiveNontrivial
      : Σ (∂Cosp × ∂Cosp)
          (λ { (p₁ , p₂) → ¬ ((Sat p₁ Objective) ↔ (Sat p₂ Objective)) })

open SocketVacuityGuards public
