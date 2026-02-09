<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

```agda
{-# OPTIONS --safe #-}
module LogOS.UniversalIR.Walkthrough where

open import LogOS.Prelude

open import LogOS.UniversalIR.Task
open import LogOS.UniversalIR.Core
open import LogOS.UniversalIR.Languages.Minsky as Minsky
open import LogOS.UniversalIR.Languages.Lambda as Lambda
open import LogOS.UniversalIR.Languages.Ethereum as Ether
open import LogOS.UniversalIR.Languages.QuantumOracle as QO
open import LogOS.UniversalIR.Languages.QuantumCircuit as QC
open import LogOS.UniversalIR.IR using (lowerToIR)
open import LogOS.UniversalIR.Schemes using
  ( UProcess
  ; OpsSteps ; run≤ᵁ ; fuelGrade
  ; minskyInterface ; lambdaInterface ; ethereumInterface ; oracleInterface
  ; minskyScheme ; lambdaScheme ; ethereumScheme ; oracleScheme
  ; minskyMachineScheme ; lambdaMachineScheme ; ethereumMachineScheme ; oracleMachineScheme
  ; quantumCircuitMachineScheme
  ; run≤-minsky ; run≤-ethereum ; run≤-oracle ; run≤-quantumCircuit
  ; run≤-fuel≡run-minsky ; run≤-fuel≡run-ethereum ; run≤-fuel≡run-oracle ; run≤-fuel≡run-quantumCircuit
  )
open import LogOS.UniversalIR.Theorems as Thm

import LogOS.Computation.Scheme as Sch
import LogOS.Computation.SchemeCategory as Cat
```

# Universal Translation Machine (Walkthrough)

CI note: this module is imported by `Tests/SmokeSurfaces.agda`, so it stays
typechecked in CI.

This walkthrough shows how five canonical programming paradigms — Minsky machines,
untyped lambda calculus, Ethereum‑like (EVM), a minimal oracle‑with‑classical‑control model,
and explicit circuits —
encode the same PA computation into a single universal IR inside LogOS.

The universal IR is `UCode` and the universal step is `stepU`. Each backend
compiles a PA task into its brand code, and can be executed with a chosen step
budget. The step-budgeted `Sch.run` wrappers are convenience; the semantic core is
the **grade-indexed** runner `Sch.run≤` parameterized by `ScaleOps`, and the fuel-free
predicates in `LogOS.Computation.Scheme` (e.g. `Sch.ComputesTo`).

## Universal process + paradigm choices

Internally, UniversalIR factors this as:

- one shared `Process` (`UProcess`) containing the universal dynamics (`stepU`),
  IR-normalisation, observation (`decode`), and cost algebra;
- five `Interface`s selecting Minsky/λ/EVM/oracle/circuit as different computation *presentations* into that shared process.
  The library keeps a `fuel : Input → ℕ` for convenience, but the preferred execution
  interface is via a **scheme index** `g : Scale` and `ScaleOps` (see `Sch.run≤` / `Cat.run≤`).

For a kernel-aligned observation, see `LogOS/UniversalIR/ObservedKernel.agda`:
an `ObsKit` packages an observation `observeU : UCode → Obs` that commutes with `stepU`,
so the boundary evolution is well-defined. The `UProcess` view keeps `observe : UCode → ℕ`
as a semantic center, but `observe` itself is not assumed to be a step homomorphism. For
other observation spaces, use `UProcessAt`/`UProcessObs` in `LogOS/UniversalIR/Schemes.agda`.

Concretely, each exported scheme is definitionally the process + its choice:

```agda
minskyScheme' : Sch.Scheme PATask ℕ
minskyScheme' = Cat.schemeFromInterface UProcess minskyInterface

minskyScheme'≡minskyScheme : minskyScheme' ≡ minskyScheme
minskyScheme'≡minskyScheme = refl
```

## The PA Task

```agda
task : PATask
task = mkTask Add 2 3

answer : ℕ
answer = eval task
```

## Compile, execute (scheme-indexed), then lower to IR

```agda
codeM : UCode
codeM = Minsky.compile task

codeL : UCode
codeL = Lambda.compile task

codeE : UCode
codeE = Ether.compile task

codeO : UCode
codeO = QO.compile task

finalM : UCode
finalM = run≤ᵁ (fuelGrade Minsky.fuel task) codeM

finalL : UCode
finalL = run≤ᵁ (fuelGrade Lambda.fuel task) codeL

finalE : UCode
finalE = run≤ᵁ (fuelGrade Ether.fuel task) codeE

finalO : UCode
finalO = run≤ᵁ (fuelGrade QO.fuel task) codeO

finalC : UCode
finalC = run≤ᵁ (fuelGrade QC.fuel task) (QC.compile task)

irM : UCode
irM = lowerToIR finalM

irL : UCode
irL = lowerToIR finalL

irE : UCode
irE = lowerToIR finalE

irO : UCode
irO = lowerToIR finalO

irC : UCode
irC = lowerToIR finalC
```

For this closed task, all backends compute the same answer; `decode` extracts it
from the canonical IR branch.

```agda
sameRun
  : (run≤-minsky (fuelGrade Minsky.fuel task) task ≡ run≤-ethereum (fuelGrade Ether.fuel task) task)
  × (run≤-ethereum (fuelGrade Ether.fuel task) task ≡ run≤-oracle (fuelGrade QO.fuel task) task)
sameRun =
  trans (run≤-fuel≡run-minsky task) (trans (Thm.minskyMachine-correct task)
    (trans (sym (Thm.ethereumMachine-correct task)) (sym (run≤-fuel≡run-ethereum task))))
  ,
  trans (run≤-fuel≡run-ethereum task) (trans (Thm.ethereumMachine-correct task)
    (trans (sym (Thm.oracleMachine-correct task)) (sym (run≤-fuel≡run-oracle task))))
```

The explicit circuit presentation also agrees (theorem-backed):

```agda
sameRun₄ :
  (run≤-minsky (fuelGrade Minsky.fuel task) task ≡ run≤-ethereum (fuelGrade Ether.fuel task) task) ×
  (run≤-ethereum (fuelGrade Ether.fuel task) task ≡ run≤-oracle (fuelGrade QO.fuel task) task) ×
  (run≤-oracle (fuelGrade QO.fuel task) task ≡ run≤-quantumCircuit (fuelGrade QC.fuel task) task)
sameRun₄ =
  fst sameRun
  ,
  snd sameRun
  ,
  trans (run≤-fuel≡run-oracle task) (trans (Thm.oracleMachine-correct task)
    (trans (sym (Thm.circuitMachine-correct task)) (sym (run≤-fuel≡run-quantumCircuit task))))
```

Here the Minsky/EVM/oracle equalities are justified by reusable theorems
(`LogOS.UniversalIR.Theorems`). The λ backend is now certified by
construction (`Lambda.compileBrand` emits Church numerals), and
`lambdaMachine-correct` proves correctness to `eval`; the raw β-reduction
compiler remains as `Lambda.compileRawBrand` if you want the explicit program.

For a fully theorem-backed statement that avoids example-only normalization,
see `LogOS/UniversalIR/Examples/Convincing.agda` (Minsky ≡ EVM for all `PATask`).
