<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Application — Universality (Universal IR) (LogOS)

```agda
module docs.Application_Universality where

-- Sync guard: these imports anchor the module paths this document references.
-- If they drift, the docs build fails.
import LogOS.Models.UniversalIR.Core
import LogOS.Models.UniversalIR.Examples
import LogOS.Models.UniversalIR.Pack
import LogOS.Packs.Universality.All

import LogOS.Domain.UniversalIR.Core.UCode
import LogOS.Domain.UniversalIR.Core.QuantumCircuit
import LogOS.Domain.UniversalIR.Languages.Minsky
import LogOS.Domain.UniversalIR.Languages.Lambda
import LogOS.Domain.UniversalIR.Languages.Ethereum
import LogOS.Domain.UniversalIR.Languages.QuantumOracle
import LogOS.Domain.UniversalIR.Languages.QuantumCircuit
import LogOS.Domain.UniversalIR.Examples.QuantumCircuit
import LogOS.Domain.UniversalIR.Pack

import LogOS.Domain.UniversalIR.Theorems
import LogOS.Domain.UniversalIR.While.Theorems
import LogOS.Domain.UniversalIR.Schemes
import LogOS.Computation.SchemeCategory
import LogOS.Computation.KernelUniversalProcess
```

This note is the single, publication-facing entrypoint for **computational
universality** in the production library.

The goal is to present computation *inside LogOS* as a **universal process**
with multiple paradigm instantiations (Turing/Minsky, λ-calculus, quantum,
Ethereum/EVM-like), all connected by explicit translations and a shared IR.

In the “scheme” view, the library defines a canonical notion of **what computation is (in LogOS)**:
as a fuel-free normalization relation (`Sch.Scheme.ComputesTo`) and its induced
observational equivalence (`Sch.ObsEq`), plus an explicit operational budget
layer (`Sch.ExecWithin` / `Sch.ReachesWithin`), rather than as a particular machine.

It also cleanly separates **algorithms** from **implementations**:
- an algorithm is a specification (`Sch.Algorithm`),
- an implementation is a scheme together with correctness (`Sch.ImplementsRun` / `Sch.ImplementsRel`).

The “Examples” are not secondary: they are **checked evidence** included in the
build. This document imports `LogOS.Models.UniversalIR.Examples`, and CI
type-checks those modules; if the example statements drift, the universality
story fails to build.

## What “universality” means here (three tiers)

This library separates three increasingly strong claims:

1. **Substrate universality (by inclusion):**
   the shared carrier `UCode` includes a standard universal machine model
   (a 4-register Minsky machine). The library does not re-prove Turing-completeness here,
   but uses this model as the universal substrate for translations and examples.

2. **Translation universality (proved for fragments):**
   for a chosen fragment/language `Input`, provide
   - explicit compilers into multiple paradigms,
   - a single shared stepper (`stepU` on `UCode`),
   - a canonical lowering/projection (`lowerToIR`),
   and then prove “same computation” as agreement after lowering/decoding.

3. **Paradigm universality (conditional / future work):**
   the strongest reading (“λ-calculus, circuits, EVM are *equivalent*
   presentations of *arbitrary* computation”) requires a uniform source language
   and total compiler correctness theorems. The architecture is designed for
   this, but the production library currently proves it only for selected
   fragments and examples.

## The core idea

- Each paradigm is a small-step semantics on a concrete code type.
- A single unified carrier (`UCode`) packages those codes.
- “Same computation” means: compile/decompile/translate between paradigms and
  prove agreement via the common observation function `observe : UCode → ℕ`
  (defined as `decode ∘ lowerToIR` in `LogOS/Domain/UniversalIR/IR.agda`).

The diagram the code enforces (via `Process`/`Choice` and `ProcessHom`) is:

```text
Input (e.g. PATask)
  ├─ compileBrandₘ : Input → MinskyCode      ──Sch.run≤ g──▶ ℕ
  ├─ compileBrandₗ : Input → LambdaCode      ──Sch.run≤ g──▶ ℕ
  ├─ compileBrandₑ : Input → EVMCode         ──Sch.run≤ g──▶ ℕ
  ├─ compileBrandₒ : Input → QuantumCode     ──Sch.run≤ g──▶ ℕ
  └─ compileBrand꜀ : Input → QuantumCircuit  ──Sch.run≤ g──▶ ℕ

Each of these “machine schemes” factors through the same semantic center:

Input ──Choice.compile──▶ state ──Step^(steps(budget g))──▶ state ──lowerToIR──▶ state ──decode──▶ ℕ
           │                         (scheme index g)             │
           └────────────────── ProcessHom ────────────┘
```

## Where the code lives

- Universal IR + languages + semantics:
  - `LogOS/Domain/UniversalIR/*`
  - The curated, stable surface: `LogOS/Models/UniversalIR/Core.agda`
- Pack skeleton (Assumptions/Claim/Pack/mkPack) for the “same computation, many
  representations” claim:
  - `LogOS/Domain/UniversalIR/Pack.agda`
  - Curated re-export: `LogOS/Models/UniversalIR/Pack.agda`
- Paradigms (examples):
  - Minsky machine: `LogOS/Domain/UniversalIR/Languages/Minsky.agda`
  - Untyped λ-calculus: `LogOS/Domain/UniversalIR/Languages/Lambda.agda`
  - EVM-like machine: `LogOS/Domain/UniversalIR/Languages/Ethereum.agda`
  - Quantum (two presentations):
    - oracle-with-classical-control: `LogOS/Domain/UniversalIR/Languages/QuantumOracle.agda`
    - explicit circuits: `LogOS/Domain/UniversalIR/Languages/QuantumCircuit.agda`
  - Tiny executable circuit sanity checks:
    - `LogOS/Domain/UniversalIR/Examples/QuantumCircuit.agda`
- “Universal computation as a process” (choices + morphisms):
  - `LogOS/Computation/SchemeCategory.agda`
  - `LogOS/Domain/UniversalIR/Schemes.agda`
- Kernel ↔ process bridge (code process observed via `decode`):
  - `LogOS/Computation/KernelUniversalProcess.agda`

## Quick import (namespaced)

```text
open import LogOS.Models.UniversalIR.Core as U
```

There is no `LogOS.Models.UniversalIR.All`; use the namespaced core import above.
If you want the bundled pack (Universality + UniversalIR), import `LogOS.Packs.Universality.All`.

Examples are intentionally separated from the core surface:

```text
open import LogOS.Models.UniversalIR.Examples as UEx
```

Notable example:
- `LogOS/Domain/UniversalIR/Examples/LambdaShowcase.agda` — raw vs certified λ compilation metrics plus a five-paradigm output snapshot.

## A good first stop

- `LogOS/Domain/UniversalIR/README.md` (map of submodules)
- `LogOS/Domain/UniversalIR/Walkthrough.lagda.md` (worked narrative with examples)

## Proof status (honest summary)

- **Universal substrate present:** Minsky is included as a branch of `UCode`
  with a total small-step semantics (`LogOS/Domain/UniversalIR/Core/UCode.agda`).
- **Translation universality (PA fragment):** `PATask` (addition/multiplication)
  is compiled to multiple paradigms and proved correct for all inputs for:
  - Minsky, λ-calculus (certified Church output), Ethereum, QuantumOracle, and Circuit
    (`LogOS/Domain/UniversalIR/Theorems.agda`).
- **Explicit circuits are real, not just a label:** there is an explicit
  basis-state circuit syntax and stepper (`LogOS/Domain/UniversalIR/Core/QuantumCircuit.agda`)
  and a circuit backend (`LogOS/Domain/UniversalIR/Languages/QuantumCircuit.agda`), with
  small runnable gate-level examples (`LogOS/Domain/UniversalIR/Examples/QuantumCircuit.agda`).
- **Costs have “physics bite”:** all UniversalIR schemes use a two-axis quantale
  cost (`LogOS/Adapters/QNat2.agda`) where costs are pairs `(unitaryWork , measurementEvents)`;
  costs are built via `work`/`meas` (and join-composed budgets `budget₂`);
  quantum `MEASURE`/`QMEASURE` steps contribute on the second axis
  (`LogOS/Domain/UniversalIR/Schemes.agda`). The same file also exposes a single
  per-step envelope `stepBudgetᵁ = budget₂ 3 1` with `stepCostᵁ≤stepBudgetᵁ`,
  so the whole coproduct `UCode` has an explicit, join-shaped cost cap per step.
- **Schemes are grade-indexed (ScaleOps):** a “scheme index” is a grade `g : Scale`,
  interpreted as a step budget via `ScaleOps` (see `Sch.run≤` and `Cat.run≤`);
  the schedule-based `Sch.run` (where the schedule is the scheme’s `fuel`) is a
  special case at grade `work (fuel t)` (i.e. `τ (fuel t)` on `QNat2`)
  (`run≤-fuel≡run-*` in `LogOS/Domain/UniversalIR/Schemes.agda`).
- **Time vs observation are independent:** `ScaleOps` reads only the work axis.
  Concretely, `run≤ᵁ (budget₂ k m) ≡ run≤ᵁ (work k)` (`run≤ᵁ-budget₂≡work`), while
  measurement cannot be “paid for” by a work-only budget (`meas1≰work` / `work1≰meas`)
  (`LogOS/Domain/UniversalIR/Schemes.agda`).
- **Operational budget transport (process morphisms):** reachability and cost
  bounds transport across representations via
  `LogOS.Computation.SchemeCategory.Semantics.ExecWithin-natural` and
  `LogOS.Computation.SchemeCategory.Semantics.ReachesWithin-natural`. This is
  used in `LogOS/Domain/UniversalIR/Examples/SchemeChoices.agda` to exhibit
  explicit budgeted Minsky executions and factor them through the universal
  coproduct process.
- **One-stroke Minsky variants:** any alternate resource accounting for the same
  Minsky small-step semantics can be wrapped as a `Process` and still factors
  through the universal semantic center (`MinskyProcessWith`, `Minsky→U-With` in
  `LogOS/Domain/UniversalIR/Schemes.agda`).
- **Circuits as families (uniform-by-bound):** to avoid claiming a single finite
  circuit is unboundedly universal, `QuantumCircuit` also exposes bounded
  compilation `compileFamilyFromU` (and `...FromMinsky`) indexed by a step bound
  (`LogOS/Domain/UniversalIR/Languages/QuantumCircuit.agda`).
- **Non-trivial non-PA example:** factorial is implemented via a While source
  and compiled to low-level backends; Minsky correctness is proved for all `n`
  (`LogOS/Domain/UniversalIR/While/Theorems.agda`).

### One-line agreement theorem (PA fragment)

The production library includes a single aggregation lemma stating agreement
between all five `PATask` paradigms (Minsky/λ/EVM/Oracle/Circuit):

- `LogOS/Domain/UniversalIR/Theorems.agda` exposes `patask-paradigms-correct`
  (now a named record) and `patask-paradigms-runEq`.
- `patask-paradigms-runEq` phrases the same statement via the generic scheme
  equivalence alias `Sch.RunEq` (standard “same function” packaging).

### Checked example: measurement cost axis

These are small executable examples (not universality theorems) showing the
second cost component is charged by measurement primitives:

- `LogOS/Domain/UniversalIR/Examples/QuantumCircuit.agda`: `qMeasure-cost`
- `LogOS/Domain/UniversalIR/Examples/QuantumOracle.agda`: `qMeasure-cost`

## Guardrails (CS-style theorems)

The universality story is guarded by three generic theorems that do not depend
on any particular paradigm:

- **Representation invariance:** `LogOS/Computation/SchemeCategory.agda`
  (`run≤-map`, `run≤-meaning-comm`).
- **Axis-independence (ScaleOps):** `LogOS/Computation/SchemeCategory.agda`
  (`Semantics.Exec≤-stepsEq`), with a concrete `QNat2` specialization
  `run≤ᵁ-budget₂≡work` in `LogOS/Domain/UniversalIR/Schemes.agda`.
- **Semantics is functorial (category façade):** `LogOS/Computation/SchemeCategory.agda`
  (`ProcessCategory`, `Semantics`).
- **Relational ↔ schedule semantics bridge:** `LogOS/Computation/Scheme.agda`
  (`FuelHalts`, `Bridge.RunEq→ObsEq`, `Bridge.ObsEq→RunEq`).
- **No omniscient deciders (diagonal barrier):** `LogOS/Theorems/Meta/NoOmniscience.agda`
  (kernel-local `noOmniscientDecider` and code-generic `noOmniscientDeciderC`).
- **No total oracles within a budget:** `LogOS/Theorems/Meta/BudgetedSeparationOutput.agda`
  (both ℕ-budgets and abstract budget predicates for graded kernels).

For convenience, the curated UniversalIR surface re-exports these under
`LogOS.Models.UniversalIR.Core.Guardrails`.
