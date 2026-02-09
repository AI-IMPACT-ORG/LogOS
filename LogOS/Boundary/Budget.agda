{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Boundary.Budget where

-- Kernel-aligned budget predicates derived from telemetry on boundary programs.
-- See CHL completeness lemmas in:
--   LogOS/Theorems/Meta/CHL/Completeness.agda
--   LogOS/Theorems/Meta/CHL/SyntaxCompleteness.agda
--   LogOS/Theorems/Meta/CHL/Definition.agda

open import LogOS.Prelude

open import LogOS.Base.Signature using (LogOSSignature)
open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Minimal.World as Worlds
open import LogOS.Minimal.Con using (BulkBoundary)
open import LogOS.Minimal.Truth as Truth
open import LogOS.Boundary.IO using (BoundaryIO)
open import LogOS.Boundary.Telemetry

module For
  {ℓ : Level}
  (Sig : LogOSSignature ℓ)
  (Q   : QAdapter ℓ)
  (W   : Worlds.WorldH Sig Q)
  (BB  : BulkBoundary ℓ)
  (H   : (let module HT = Truth.HomotypicalTruth Sig Q W in HT.HLayer) BB)
  (B   : BoundaryIO Sig Q W BB H)
  (T   : TelemetryTrace ℓ)
  (P   : ProgramTelemetryPort Sig Q W BB H B T)
  where

  open LogOSSignature Sig
  open TelemetryTrace T
  open ProgramTelemetryPort P

  -- Budget on boundary programs (∂Cosp): an observation is admissible if its
  -- telemetry trace is below the chosen budget trace.
  Budget∂ : Trace → ∂Cosp → Set ℓ
  Budget∂ b p = _⊑T_ (observe-∂ p) b

  -- Budget on full observations (Cosp), routed through `to∂`.
  BudgetCosp : Trace → Cosp → Set ℓ
  BudgetCosp b w = Budget∂ b (to∂ w)

  Budget : Set (lsuc ℓ)
  Budget = Cosp → Set ℓ

  budget-from-trace : Trace → Budget
  budget-from-trace b w = BudgetCosp b w
