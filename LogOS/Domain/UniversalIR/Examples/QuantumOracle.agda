{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Examples.QuantumOracle where

open import LogOS.Prelude

open import LogOS.Domain.UniversalIR.Core
open import LogOS.Domain.UniversalIR.Std using (decodeChurch-church)
import LogOS.Computation.Scheme as Sch
import LogOS.Computation.SchemeCategory as Cat
open import LogOS.Domain.UniversalIR.Schemes using (QuantumOracleProcess; meas; meas-zero; meas-+; budget₂; meas≤budget₂; QSteps)
open import LogOS.Minimal.Adapter using (QAdapter)

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

qMeasure-cost : Sch.cost qoScheme qMeasure ≡ meas 1
qMeasure-cost = refl

qMeasure-cost≤budget : QAdapter._≤s_ QSteps (Sch.cost qoScheme qMeasure) (budget₂ 0 1)
qMeasure-cost≤budget rewrite qMeasure-cost = meas≤budget₂ 0 1

-- Using `meas-zero`: 0 steps costs exactly 0 measurements.
qMeasure-costAt0 : Sch.costAt qoScheme 0 qMeasure ≡ meas 0
qMeasure-costAt0 = sym meas-zero

-- Using `meas-+`: sequential measurements add along the second quantale axis.

qoChoice2 : Cat.Choice QuantumCode QuantumOracleProcess
qoChoice2 = record { compile = (λ q → q) ; fuel = (λ _ → 2) }

qoScheme2 : Sch.Scheme QuantumCode ℕ
qoScheme2 = Cat.schemeFromChoice QuantumOracleProcess qoChoice2

qMeasure2 : QuantumCode
qMeasure2 = mkQ 0 0 0 0 0 (true ∷ []) (MEASURE 0 0 1 ∷ MEASURE 0 0 1 ∷ QHALT ∷ [])

qMeasure2-cost : Sch.cost qoScheme2 qMeasure2 ≡ meas 2
qMeasure2-cost = refl

qMeasure2-cost-factor
  : Sch.cost qoScheme2 qMeasure2 ≡ QAdapter._·_ QSteps (meas 1) (meas 1)
qMeasure2-cost-factor =
  trans qMeasure2-cost (meas-+ 1 1)

-- Sanity: the run still produces a Church-decoded numeral (here: 0).
qMeasure-runs-to-0 : Sch.run qoScheme qMeasure ≡ 0
qMeasure-runs-to-0 = decodeChurch-church 0
