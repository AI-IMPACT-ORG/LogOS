{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Physics.Implementable where

open import LogOS.Prelude

open import LogOS.Domain.UniversalIR.Core
open import LogOS.Computation.EvolutionOperator public using (EvolOperator)

-- Minimal “implementable operator” shim for the UniversalIR carrier.
-- This is intentionally lightweight; more detailed complexity/physics packs live
-- under `Models/Universality/*`.

EO-UCode : EvolOperator UCode stepU
EO-UCode = record
  { H = UCode
  ; embed = λ c → c
  ; Op = stepU
  ; intertwine = λ _ → refl
  }
