{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Examples.QuantumOracle where

open import LogOS.Prelude

open import LogOS.Domain.UniversalIR.Core
open import LogOS.Domain.UniversalIR.Std using (decodeChurch-church)
import LogOS.Computation.Scheme as Sch
import LogOS.Computation.SchemeCategory as Cat
open import LogOS.Domain.UniversalIR.Schemes using (QuantumOracleProcess)

open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)

-- EXAMPLE (argument): the non-unitary “measurement axis” shows up in cost.
--
-- This example uses the oracle-with-control instruction `MEASURE`. The PA
-- compilers intentionally avoid `MEASURE` (so correctness can be derived from
-- Minsky by erasure), but the primitive is present and charged on the second
-- axis of the `QNat2` cost adapter.

qoChoice : Cat.Choice QuantumCode QuantumOracleProcess
qoChoice = record { compile = (λ q → q) ; fuel = (λ _ → 1) }

qoScheme : Sch.Scheme QuantumCode ℕ
qoScheme = Cat.schemeFromChoice QuantumOracleProcess qoChoice

qMeasure : QuantumCode
qMeasure = mkQ 0 0 0 0 0 (true ∷ []) (MEASURE 0 0 1 ∷ QHALT ∷ [])

qMeasure-cost : Sch.cost qoScheme qMeasure ≡ (0 , 1)
qMeasure-cost = refl

-- Sanity: the run still produces a Church-decoded numeral (here: 0).
qMeasure-runs-to-0 : Sch.run qoScheme qMeasure ≡ 0
qMeasure-runs-to-0 = decodeChurch-church 0
