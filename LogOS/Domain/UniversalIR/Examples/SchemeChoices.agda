{-
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Domain.UniversalIR.Examples.SchemeChoices where

open import LogOS.Prelude

import LogOS.Computation.Scheme as Sch
import LogOS.Computation.SchemeCategory as Cat

open import LogOS.Domain.UniversalIR.Task using (PATask; mkTask; Add; Mul; eval)
open import LogOS.Domain.UniversalIR.Core.Minsky using (MinskyCode)
import LogOS.Domain.UniversalIR.Languages.Minsky as Minsky
open import LogOS.Domain.UniversalIR.Schemes using
  ( UProcess
  ; minskyScheme
  ; ethereumScheme
  ; minskyMachineScheme
  ; ethereumMachineScheme
  ; minskyMachineChoice
  ; ethereumMachineChoice
  ; Minsky→U
  ; Minsky→UCost
  ; Ethereum→U
  ; Ethereum→UCost
  ; oracleMachineScheme
  ; quantumCircuitMachineScheme
  ; oracleMachineChoice
  ; quantumCircuitMachineChoice
  ; Oracle→U
  ; Oracle→UCost
  ; Circuit→U
  ; Circuit→UCost
  ; MinskyProcessWith
  ; Minsky→U-With
  )
import LogOS.Domain.UniversalIR.Theorems as Thm

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
  : ∀ t → Sch.run (Cat.schemeFromChoice UProcess (Cat.mapChoice Minsky→U minskyMachineChoice)) t
        ≡ Sch.run minskyMachineScheme t
minskyFactorsThroughU t = Cat.run-comm Minsky→U minskyMachineChoice t

ethereumFactorsThroughU
  : ∀ t → Sch.run (Cat.schemeFromChoice UProcess (Cat.mapChoice Ethereum→U ethereumMachineChoice)) t
        ≡ Sch.run ethereumMachineScheme t
ethereumFactorsThroughU t = Cat.run-comm Ethereum→U ethereumMachineChoice t

oracleFactorsThroughU
  : ∀ t → Sch.run (Cat.schemeFromChoice UProcess (Cat.mapChoice Oracle→U oracleMachineChoice)) t
        ≡ Sch.run oracleMachineScheme t
oracleFactorsThroughU t = Cat.run-comm Oracle→U oracleMachineChoice t

circuitFactorsThroughU
  : ∀ t → Sch.run (Cat.schemeFromChoice UProcess (Cat.mapChoice Circuit→U quantumCircuitMachineChoice)) t
        ≡ Sch.run quantumCircuitMachineScheme t
circuitFactorsThroughU t = Cat.run-comm Circuit→U quantumCircuitMachineChoice t

-- EXAMPLE (argument): budget transport (cost) via `ProcessHomCost`.
--
-- Costs are preserved when factoring a machine scheme through the universal
-- semantic center, provided step-cost commutes (which it does by construction
-- for the `UCode` injections).

minskyCostFactorsThroughU
  : ∀ t → Sch.cost (Cat.schemeFromChoice UProcess (Cat.mapChoice Minsky→U minskyMachineChoice)) t
        ≡ Sch.cost minskyMachineScheme t
minskyCostFactorsThroughU t = Cat.cost-comm Minsky→UCost minskyMachineChoice t

ethereumCostFactorsThroughU
  : ∀ t → Sch.cost (Cat.schemeFromChoice UProcess (Cat.mapChoice Ethereum→U ethereumMachineChoice)) t
        ≡ Sch.cost ethereumMachineScheme t
ethereumCostFactorsThroughU t = Cat.cost-comm Ethereum→UCost ethereumMachineChoice t

oracleCostFactorsThroughU
  : ∀ t → Sch.cost (Cat.schemeFromChoice UProcess (Cat.mapChoice Oracle→U oracleMachineChoice)) t
        ≡ Sch.cost oracleMachineScheme t
oracleCostFactorsThroughU t = Cat.cost-comm Oracle→UCost oracleMachineChoice t

circuitCostFactorsThroughU
  : ∀ t → Sch.cost (Cat.schemeFromChoice UProcess (Cat.mapChoice Circuit→U quantumCircuitMachineChoice)) t
        ≡ Sch.cost quantumCircuitMachineScheme t
circuitCostFactorsThroughU t = Cat.cost-comm Circuit→UCost quantumCircuitMachineChoice t

-- --------------------------------------------------------------------------
-- One concrete “same meaning, wildly different cost profile” example.

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

minsky23-cost : Sch.cost minskyScheme task23 ≡ (37 , 0)
minsky23-cost = refl

ethereum23-cost : Sch.cost ethereumScheme task23 ≡ (4 , 0)
ethereum23-cost = refl

-- --------------------------------------------------------------------------
-- One-stroke “Minsky variants”: different resource accounting, same semantics.

flatCost : MinskyCode → (ℕ × ℕ)
flatCost _ = (0 , 0)

minskyVariantScheme : Sch.Scheme PATask ℕ
minskyVariantScheme =
  Cat.schemeFromChoice
    (MinskyProcessWith flatCost)
    (record { compile = Minsky.compileBrand
            ; fuel    = Minsky.fuel
            })

minskyVariantFactorsThroughU
  : ∀ t →
    Sch.run (Cat.schemeFromChoice UProcess (Cat.mapChoice (Minsky→U-With flatCost)
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
