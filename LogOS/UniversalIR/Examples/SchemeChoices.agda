{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.UniversalIR.Examples.SchemeChoices where

open import LogOS.Prelude

import LogOS.Computation.Scheme as Sch
import LogOS.Computation.SchemeCategory as Cat
open import LogOS.Computation.Core using (iterate)

open import LogOS.UniversalIR.Task using (PATask; mkTask; Add; Mul; eval)
open import LogOS.UniversalIR.Core.Minsky using (MinskyCode)
import LogOS.UniversalIR.Languages.Minsky as Minsky
open import LogOS.UniversalIR.Schemes using
  ( UProcess
  ; minskyScheme
  ; ethereumScheme
  ; Budget
  ; work
  ; budget₂
  ; work≤budget₂
  ; three·
  ; QSteps
  ; minskyInterface
  ; interfaceScheme-execWithinAt≤budget₂3n,n
  ; interfaceScheme-execWithinSplit≤budget₂3n,n
  ; minskyMachineScheme
  ; ethereumMachineScheme
  ; minskyMachineInterface
  ; ethereumMachineInterface
  ; Minsky→U
  ; Minsky→UCost
  ; Ethereum→U
  ; Ethereum→UCost
  ; oracleMachineScheme
  ; quantumCircuitMachineScheme
  ; oracleMachineInterface
  ; quantumCircuitMachineInterface
  ; Oracle→U
  ; Oracle→UCost
  ; Circuit→U
  ; Circuit→UCost
  ; MinskyProcessWith
  ; Minsky→U-With
  )
import LogOS.UniversalIR.Theorems as Thm
open import LogOS.Minimal.Adapter using (QAdapter)
open QAdapter QSteps using (_·_)

-- EXAMPLE (argument): scheme-centric view (“machines as schemes”) and factorization lemmas.

-- --------------------------------------------------------------------------
-- Scheme view: machines are schemes, and all paradigms factor through the same
-- universal semantic center (the universal `UProcess`).

minskyMachine-sound : ∀ t → Sch.run minskyMachineScheme t ≡ eval t
minskyMachine-sound = Thm.minskyMachine-correct

ethereumMachine-sound : ∀ t → Sch.run ethereumMachineScheme t ≡ eval t
ethereumMachine-sound = Thm.ethereumMachine-correct

minsky≡ethereum : ∀ t → Sch.run minskyMachineScheme t ≡ Sch.run ethereumMachineScheme t
minsky≡ethereum t = trans (minskyMachine-sound t) (sym (ethereumMachine-sound t))

-- Explicit factoring through the universal process via `ProcessHom`.

minskyFactorsThroughU
  : ∀ t → Sch.run (Cat.schemeFromInterface UProcess (Cat.mapInterface Minsky→U minskyMachineInterface)) t
        ≡ Sch.run minskyMachineScheme t
minskyFactorsThroughU t = Cat.run-comm Minsky→U minskyMachineInterface t

ethereumFactorsThroughU
  : ∀ t → Sch.run (Cat.schemeFromInterface UProcess (Cat.mapInterface Ethereum→U ethereumMachineInterface)) t
        ≡ Sch.run ethereumMachineScheme t
ethereumFactorsThroughU t = Cat.run-comm Ethereum→U ethereumMachineInterface t

oracleFactorsThroughU
  : ∀ t → Sch.run (Cat.schemeFromInterface UProcess (Cat.mapInterface Oracle→U oracleMachineInterface)) t
        ≡ Sch.run oracleMachineScheme t
oracleFactorsThroughU t = Cat.run-comm Oracle→U oracleMachineInterface t

circuitFactorsThroughU
  : ∀ t → Sch.run (Cat.schemeFromInterface UProcess (Cat.mapInterface Circuit→U quantumCircuitMachineInterface)) t
        ≡ Sch.run quantumCircuitMachineScheme t
circuitFactorsThroughU t = Cat.run-comm Circuit→U quantumCircuitMachineInterface t

-- EXAMPLE (argument): budget transport (cost) via `ProcessHomCost`.
--
-- Costs are transported *laxly* when factoring a machine scheme through the
-- universal semantic center: the universal presentation does not increase the
-- observed cost profile (here the grade map is the identity).

minskyCostFactorsThroughU
  : ∀ t
  → QAdapter._≤s_ QSteps
      (Sch.cost (Cat.schemeFromInterface UProcess (Cat.mapInterface Minsky→U minskyMachineInterface)) t)
      (Sch.cost minskyMachineScheme t)
minskyCostFactorsThroughU t =
  Cat.costAt-map≤
    Minsky→UCost
    minskyMachineInterface
    (Sch.fuel minskyMachineScheme t)
    t

ethereumCostFactorsThroughU
  : ∀ t
  → QAdapter._≤s_ QSteps
      (Sch.cost (Cat.schemeFromInterface UProcess (Cat.mapInterface Ethereum→U ethereumMachineInterface)) t)
      (Sch.cost ethereumMachineScheme t)
ethereumCostFactorsThroughU t =
  Cat.costAt-map≤
    Ethereum→UCost
    ethereumMachineInterface
    (Sch.fuel ethereumMachineScheme t)
    t

oracleCostFactorsThroughU
  : ∀ t
  → QAdapter._≤s_ QSteps
      (Sch.cost (Cat.schemeFromInterface UProcess (Cat.mapInterface Oracle→U oracleMachineInterface)) t)
      (Sch.cost oracleMachineScheme t)
oracleCostFactorsThroughU t =
  Cat.costAt-map≤
    Oracle→UCost
    oracleMachineInterface
    (Sch.fuel oracleMachineScheme t)
    t

circuitCostFactorsThroughU
  : ∀ t
  → QAdapter._≤s_ QSteps
      (Sch.cost (Cat.schemeFromInterface UProcess (Cat.mapInterface Circuit→U quantumCircuitMachineInterface)) t)
      (Sch.cost quantumCircuitMachineScheme t)
circuitCostFactorsThroughU t =
  Cat.costAt-map≤
    Circuit→UCost
    quantumCircuitMachineInterface
    (Sch.fuel quantumCircuitMachineScheme t)
    t

-- Operational budget transport: the whole “executed within budget” witness is
-- preserved when factoring a machine scheme through the universal process.

minskyExecWithinFactorsThroughU
  : ∀ n m b m'
  → Sch.ExecWithin minskyMachineScheme n m b m'
  → Sch.ExecWithin
      (Cat.schemeFromInterface UProcess (Cat.mapInterface Minsky→U minskyMachineInterface))
      n
      (Cat.ProcessHom.map Minsky→U m)
      b
      (Cat.ProcessHom.map Minsky→U m')
minskyExecWithinFactorsThroughU n m b m' ew =
  Cat.ExecWithin-map Minsky→UCost minskyMachineInterface n m b m' ew

-- --------------------------------------------------------------------------
-- One concrete “same `Sch.run` behaviour, wildly different cost profile” example.

task23 : PATask
task23 = mkTask Mul 2 3

answer23 : ℕ
answer23 = eval task23

answer23≡6 : answer23 ≡ 6
answer23≡6 = refl

minsky23-ok : Sch.run minskyScheme task23 ≡ 6
minsky23-ok = trans (Thm.minskyMachine-correct task23) answer23≡6

ethereum23-ok : Sch.run ethereumScheme task23 ≡ 6
ethereum23-ok = trans (Thm.ethereumMachine-correct task23) answer23≡6

minsky23-cost : Sch.cost minskyScheme task23 ≡ work 37
minsky23-cost = refl

ethereum23-cost : Sch.cost ethereumScheme task23 ≡ work 4
ethereum23-cost = refl

minsky23-cost≤budget : QAdapter._≤s_ QSteps (Sch.cost minskyScheme task23) (budget₂ 37 0)
minsky23-cost≤budget rewrite minsky23-cost = work≤budget₂ 37 0

-- Same example, but in the operational “execute within budget” form:
-- the universal cost envelope yields a concrete `ExecWithin` witness.

minsky23-execWithinBudget :
  Sch.ExecWithin
    minskyScheme
    (Sch.fuel minskyScheme task23)
    (Sch.compile minskyScheme task23)
    (budget₂ (three· (Sch.fuel minskyScheme task23)) (Sch.fuel minskyScheme task23))
    (Sch.exec minskyScheme (Sch.fuel minskyScheme task23) task23)
minsky23-execWithinBudget =
  interfaceScheme-execWithinAt≤budget₂3n,n minskyInterface task23

-- And budgeted executions compose under prequantale multiplication (split example).

minsky23-execWithinBudgetSplit :
  Sch.ExecWithin
    minskyScheme
    (10 + 27)
    (Sch.compile minskyScheme task23)
    (budget₂ (three· 10) 10 · budget₂ (three· 27) 27)
    (iterate (Sch.Scheme.Comp minskyScheme) 27
      (iterate (Sch.Scheme.Comp minskyScheme) 10 (Sch.compile minskyScheme task23)))
minsky23-execWithinBudgetSplit =
  interfaceScheme-execWithinSplit≤budget₂3n,n minskyInterface 10 27 (Sch.compile minskyScheme task23)

-- Machine-level (Minsky state space) run, and its transport into the universal
-- semantic center via `Minsky→UCost`.

minskyMachine23-execWithinFuel :
  Sch.ExecWithin
    minskyMachineScheme
    (Sch.fuel minskyMachineScheme task23)
    (Sch.compile minskyMachineScheme task23)
    (Sch.cost minskyMachineScheme task23)
    (Sch.exec minskyMachineScheme (Sch.fuel minskyMachineScheme task23) task23)
minskyMachine23-execWithinFuel =
  LogOS.Prelude.refl , QAdapter.≤s-refl QSteps

minskyMachine23-execWithinFuelThroughU :
  Sch.ExecWithin
    (Cat.schemeFromInterface UProcess (Cat.mapInterface Minsky→U minskyMachineInterface))
    (Sch.fuel minskyMachineScheme task23)
    (Cat.ProcessHom.map Minsky→U (Sch.compile minskyMachineScheme task23))
    (Sch.cost minskyMachineScheme task23)
    (Cat.ProcessHom.map Minsky→U
      (Sch.exec minskyMachineScheme (Sch.fuel minskyMachineScheme task23) task23))
minskyMachine23-execWithinFuelThroughU =
  minskyExecWithinFactorsThroughU
    (Sch.fuel minskyMachineScheme task23)
    (Sch.compile minskyMachineScheme task23)
    (Sch.cost minskyMachineScheme task23)
    (Sch.exec minskyMachineScheme (Sch.fuel minskyMachineScheme task23) task23)
    minskyMachine23-execWithinFuel

-- --------------------------------------------------------------------------
-- One-stroke “Minsky variants”: different resource accounting, same `Sch.run` behaviour.

flatCost : MinskyCode → Budget
flatCost _ = QAdapter.⊥s (Sch.Scheme.Q minskyMachineScheme)

minskyVariantScheme : Sch.Scheme PATask ℕ
minskyVariantScheme =
  Cat.schemeFromInterface
    (MinskyProcessWith flatCost)
    (record { compile = Minsky.compileBrand
            ; fuel    = Minsky.fuel
            })

minskyVariantFactorsThroughU
  : ∀ t →
    Sch.run (Cat.schemeFromInterface UProcess (Cat.mapInterface (Minsky→U-With flatCost)
      (record { compile = Minsky.compileBrand
              ; fuel    = Minsky.fuel
              }))) t
      ≡ Sch.run minskyVariantScheme t
minskyVariantFactorsThroughU t =
  Cat.run-comm (Minsky→U-With flatCost)
    (record { compile = Minsky.compileBrand
            ; fuel    = Minsky.fuel
            })
    t
