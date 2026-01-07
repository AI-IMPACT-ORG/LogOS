{-
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Examples.QuantumCircuit where

open import LogOS.Prelude

open import LogOS.Domain.UniversalIR.Core
open import LogOS.Domain.UniversalIR.IR using (observe)
open import LogOS.Domain.UniversalIR.Std using (decodeChurch-church)
open import LogOS.Domain.UniversalIR.Task using (PATask; mkTask; Add)
open import LogOS.Domain.UniversalIR.Languages.QuantumCircuit as QC using (compilePrepBrand; fuelPrep)
import LogOS.Computation.Scheme as Sch
import LogOS.Computation.SchemeCategory as Cat
open import LogOS.Domain.UniversalIR.Schemes using (QuantumCircuitProcess; meas; meas-zero; meas-+; budget₂; meas≤budget₂; QSteps)
open import LogOS.Minimal.Adapter using (QAdapter)

open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)

-- EXAMPLE (argument): explicit basis-state circuit semantics (including a costed measurement axis).

-- Small, concrete sanity checks for the explicit basis-state circuit semantics.
--
-- These are not “universality” theorems; they are tiny executable examples that
-- make the circuit primitive layer tangible in the production surface.
--
-- The examples are phrased in the Scheme view: the circuit machine is a
-- `Process`, and we choose "compile = id" and a fixed step budget.

qcChoice : Cat.Choice QuantumCircuitCode QuantumCircuitProcess
qcChoice = record { compile = (λ q → q) ; fuel = (λ _ → 1) }

qcScheme : Sch.Scheme QuantumCircuitCode ℕ
qcScheme = Cat.schemeFromChoice QuantumCircuitProcess qcChoice

-- 1) NOT gate on wire 0

qNOT : QuantumCircuitCode
qNOT = mkQC 0 1 (false ∷ []) (QX 0 ∷ QCHALT ∷ [])

qNOT-runs-to-1 : Sch.run qcScheme qNOT ≡ 1
qNOT-runs-to-1 = decodeChurch-church 1

-- 2) CNOT with control 0, target 1 on |10⟩ ↦ |11⟩

qCNOT : QuantumCircuitCode
qCNOT = mkQC 0 2 (true ∷ false ∷ []) (QCNOT 0 1 ∷ QCHALT ∷ [])

qCNOT-runs-to-3 : Sch.run qcScheme qCNOT ≡ 3
qCNOT-runs-to-3 = decodeChurch-church 3

-- 3) Toffoli (cc-not) on |110⟩ ↦ |111⟩

qTOFF : QuantumCircuitCode
qTOFF = mkQC 0 3 (true ∷ true ∷ false ∷ []) (QTOFF 0 1 2 ∷ QCHALT ∷ [])

qTOFF-runs-to-7 : Sch.run qcScheme qTOFF ≡ 7
qTOFF-runs-to-7 = decodeChurch-church 7

-- EXAMPLE (argument): the measurement axis shows up in cost.
--
-- `QMEASURE` contributes on the second component of the `QNat2` cost.

qMeasure : QuantumCircuitCode
qMeasure = mkQC 0 1 (true ∷ []) (QMEASURE 0 0 1 ∷ QCHALT ∷ [])

qMeasure-cost : Sch.cost qcScheme qMeasure ≡ meas 1
qMeasure-cost = refl

qMeasure-cost≤budget : QAdapter._≤s_ QSteps (Sch.cost qcScheme qMeasure) (budget₂ 0 1)
qMeasure-cost≤budget rewrite qMeasure-cost = meas≤budget₂ 0 1

-- Using `meas-zero`: 0 steps costs exactly 0 measurements.
qMeasure-costAt0 : Sch.costAt qcScheme 0 qMeasure ≡ meas 0
qMeasure-costAt0 = sym meas-zero

-- Using `meas-+`: sequential measurements add along the second quantale axis.

qcChoice2 : Cat.Choice QuantumCircuitCode QuantumCircuitProcess
qcChoice2 = record { compile = (λ q → q) ; fuel = (λ _ → 2) }

qcScheme2 : Sch.Scheme QuantumCircuitCode ℕ
qcScheme2 = Cat.schemeFromChoice QuantumCircuitProcess qcChoice2

qMeasure2 : QuantumCircuitCode
qMeasure2 = mkQC 0 1 (true ∷ []) (QMEASURE 0 0 1 ∷ QMEASURE 0 0 1 ∷ QCHALT ∷ [])

qMeasure2-cost : Sch.cost qcScheme2 qMeasure2 ≡ meas 2
qMeasure2-cost = refl

qMeasure2-cost-factor
  : Sch.cost qcScheme2 qMeasure2 ≡ QAdapter._·_ QSteps (meas 1) (meas 1)
qMeasure2-cost-factor =
  trans qMeasure2-cost (meas-+ 1 1)

-- 4) State-preparation compiler artifact (basis-state “circuit compilation”)

tAdd12 : PATask
tAdd12 = mkTask Add 1 2

qAdd12 : QuantumCircuitCode
qAdd12 = QC.compilePrepBrand tAdd12

qAdd12-runs-to-3 : observe (simulate (QC.fuelPrep tAdd12) (UQC qAdd12)) ≡ 3
qAdd12-runs-to-3 = decodeChurch-church 3
