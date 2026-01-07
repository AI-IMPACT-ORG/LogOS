{-
  LogOS: an Agda research library for foundational logic system architecture.
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.Complexity.ResourceSchemaGraded where

open import LogOS.Prelude

open import LogOS.Minimal.Adapter using (QAdapter)
open import LogOS.Domain.Complexity.Poly using (PolyPred)
import LogOS.Domain.Complexity.ResourceSchemaG as RG
import LogOS.Domain.Complexity.PolyGrade as PG

-- Grade-native resource schema: time/cost lives in the grade.
-- This wrapper specializes `ResourceSchemaG.Bounded` to the “poly via gradeBound” class
-- (using `PolyGrade.FromNat`), and re-exports the same API names.

module For {ℓI ℓ ℓQ : Level}
           (Input : Set ℓI)
           (size  : Input → ℕ)
           (Pℕ    : PolyPred)
           (Q     : QAdapter ℓQ)
  (gradeBound : ℕ → QAdapter.Scale Q)
  where

  Grade : Set ℓQ
  Grade = QAdapter.Scale Q

  infix 4 _≤g_
  _≤g_ : Grade → Grade → Set ℓQ
  _≤g_ = QAdapter._≤s_ Q

  module Base = RG.For {ℓI = ℓI} {ℓ = ℓ} {ℓQ = ℓQ} Input size Q
  open Base public using
    ( Language
    ; QTimeDeciderG
    ; toDeciderG
    ; mapQTimeDeciderG
    ; ThroughputG
    ; CapacityG
    ; HardG
    ; notTimeBoundedG
    )

  module PGN = PG.FromNat Q Pℕ gradeBound
  module Bounded = Base.Bounded (PG.PolyPredG.isPolyG PGN.polyPredG)

  open Bounded public using
    ( QTimeDecider
    ; toQTimeDeciderG
    ; toDecider
    ; mapQTimeDecider
    ; Hard
    ; notTimeBounded
    )

  -- Compatibility names (historical): “poly-time” means the chosen bound class.
  Throughput = ThroughputG
  Capacity   = CapacityG

  notPolyTime = notTimeBounded
