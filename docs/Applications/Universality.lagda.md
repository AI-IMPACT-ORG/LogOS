<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Application — Universality (Universal IR) (LogOS)

```agda
{-# OPTIONS --safe #-}
module docs.Applications.Universality where

-- Sync guard: these imports anchor the module paths this document references.
-- If they drift, the docs build fails.
import LogOS.Packs.Universality.Surface
```

This note is the single, publication-facing entrypoint for **computational
universality** in the production library. It presents a checked universality
story: a shared carrier, a total stepper, and explicit observation/translation
layers.

The goal is to present computation *inside LogOS* as a **universal process
model**: multiple internal languages (Minsky, untyped λ-calculus, quantum
oracle/circuit models, a small EVM-like language) share a single semantic center
and explicit translations.

Naming note (guardrail): “Minsky”, “λ”, “quantum”, “EVM-like” refer to internal
formal languages in `LogOS/Domain/UniversalIR/Languages/*`. Any alignment to
external systems is interpretive and must be justified by explicit adapters and
assumptions; the literal claims are only about the included semantics.

## Curated surfaces (stable)

- Universal IR core: `LogOS/Packs/UniversalIR/Core.agda`
- Agreement theorem (paper-facing): `LogOS/Packs/UniversalIR/Agreement.agda`
- Stable lock surface (IR + agreement + meta-language): `LogOS/Packs/Universality/Surface.agda`
- Meta-language refinement (schemes/processes): `LogOS/MetaLanguage/All.agda`
- Core universality surface (lightweight, minimal exports): `LogOS/Packs/Universality/Core.agda`
- Compiler-correctness packaging (compile + explicit fuel budgets):
  `LogOS/Domain/UniversalIR/CompilerCorrectness.agda`
- Kernel/port view for the core (boundary port + code port):
  `LogOS/Packs/Universality/Core.agda` (module `Ports`)
- Kernel/port view for UniversalIR observation kits:
  `LogOS/Packs/UniversalIR/Kernel.agda` (module `ObservedPorts`)

Boundaries are explicit: the strong “all paradigms are equivalent for all inputs”
claim is *not* assumed; the library proves agreement for selected fragments and
examples, and exposes the machinery needed to extend it.

Two complementary universality surfaces live side by side:
- **UniversalIR** is the heavy, multi-paradigm IR with translations and agreement.
- **Universality (core)** is a small, total, executable universality sketch
  (`LogOS.Packs.Universality.Core`) intended for lightweight reasoning. It now
  re‑exports only `LogOS.Domain.Universality.Core`, with the scheme wrapper under
  `CoreScheme` to keep the surface tight. The kernel view refines the **boundary
  preorder** to observational equality (`observeCore`) and supplies a canonical
  representative map (`Flow = canonCore`). Its H-tier truth is intentionally
  vacuous, so canonical ports should be read as structural wiring unless you add
  separate non-vacuity/meaningfulness assumptions.

In the “scheme” view, the library defines a canonical notion of **what computation is (in LogOS)**:
as a fuel-free computation relation (`Sch.Scheme.ComputesTo`, i.e. “there exists a run to a definitional fixed point”)
and its induced observational equivalence (`Sch.ObsEq`), plus an explicit operational budget
layer (`Sch.ExecWithin` / `Sch.ReachesWithin`), rather than as a particular machine.
For quotient-friendly “stability up to observation”, use the preorder/closure-stable variants
(`halts`, `ComputesTo≈`, `StabilizesTo`) in `LogOS/Computation/Scheme.agda`.

It also cleanly separates **algorithms** from **implementations**:
- an algorithm is a specification (`Sch.Algorithm`),
- an implementation is a scheme together with correctness (`Sch.ImplementsRun` / `Sch.ImplementsRel`).

The “Examples” are not secondary: they are **checked evidence** included in the
build. This document imports `LogOS.Packs.Universality.Surface`, which
re-exports (and therefore type-checks) `LogOS.Packs.UniversalIR.Examples`. CI
type-checks the docs entrypoints; if the example statements drift, the
universality story fails to build.

## What “universality” means here (three tiers)

1. **Substrate universality (by inclusion):**
   the shared carrier `UCode` includes a universal machine model (Minsky).
   We do not re‑prove Turing‑completeness; we use the model as a common substrate.

2. **Translation universality (proved for fragments):**
   for a chosen task/fragment, provide transpilers into multiple paradigms,
   share a single stepper on `UCode`, and prove agreement after lowering/decoding.

3. **Paradigm universality (conditional):**
   full equivalence of paradigms for arbitrary computation would require
   uniform source languages and total transpiler correctness; the architecture
   supports this, but the production library proves it only for selected fragments.

## Relation to literature

This application is meant to subsume standard universality narratives while
making translations and budgets explicit:

- **Turing-completeness comparisons:** the usual Minsky/lambda/Turing story is
  recovered at the level of encodings into a common carrier, then proving
  observational agreement for the covered fragments via the shared observation function.
- **Transpiler correctness / IR design:** the agreement theorems are stated as
  proof obligations about transpilation and decoding, matching the transpiler
  correctness literature but with a universal IR as the semantic center.
- **Categorical/process semantics:** the `Process`/`ProcessHom` interface is a
  categorical packaging of computation and translation. When you also want to
  transport cost/budget claims, use `ProcessHomCost` (or `ProcessHomCostWithGrade`)
  from `LogOS/Computation/SchemeCategory.agda`.

## The core idea

- Each paradigm is a small-step semantics on a concrete code type.
- A single unified carrier (`UCode`) packages those codes.
- “Same computation” means: transpile/decompile/translate between paradigms and
  prove agreement via the common observation function `observe : UCode → ℕ`
  (defined as `decode ∘ lowerToIR` in `LogOS/Domain/UniversalIR/IR.agda`).
  For a kernel-aligned observation space, use `ObsKit` in
  `LogOS/Domain/UniversalIR/ObservedKernel.agda`: it packages any observation
  `observeU : UCode → Obs` that commutes with `stepU` (a true step homomorphism).
  If you want a different output space in the scheme view, use `UProcessAt` or
  `UProcessObs` from `LogOS/Domain/UniversalIR/Schemes.agda`, plus the `*ProcessAt`
  constructors (e.g., `MinskyProcessAt`) for machine-level schemes.

The diagram the code enforces (via `Process`/`Choice` and `ProcessHom`) is:

The `compileBrand*` functions below are the concrete transpilers (the names
remain “compile” to reflect their conventional API surface).

```text
Input (e.g. PATask; see also `UCodeTask` for “arbitrary tasks”)
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

`ProcessHom` is the explicit semantic transport. If you also want cost/budget
claims to be preserved by translation, use `ProcessHomCost` / `ProcessHomCostWithGrade`.

## Where the code lives

- Universal IR + languages + semantics:
  - `LogOS/Domain/UniversalIR/*`
  - The curated, stable surface: `LogOS/Packs/UniversalIR/Core.agda`
- “Arbitrary tasks” (treat UniversalIR code as the task language):
  - `LogOS/Domain/UniversalIR/ArbitraryTasks.agda`
- Observed-kernel view (step-homomorphic observation kits):
  - `LogOS/Domain/UniversalIR/ObservedKernel.agda`
  - Canonical port view for any observation kit:
    `LogOS/Domain/UniversalIR/ObservedKernel.agda` (module `Ports`)
  - Pack-level defaults for common kits:
    `LogOS/Packs/UniversalIR/Kernel.agda` (module `ObservedPorts`)
- Pack skeleton (Assumptions/Claim/Pack/mkPack) for the “same computation, many
  representations” claim:
  - `LogOS/Domain/UniversalIR/Pack.agda`
  - Curated re-export: `LogOS/Packs/UniversalIR/Pack.agda`
- Agreement theorem (paper surface):
  - `LogOS/Packs/UniversalIR/Agreement.agda`
- Compiler correctness pack (end-to-end with explicit fuel):
  - `LogOS/Domain/UniversalIR/CompilerCorrectness.agda`
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
open import LogOS.Packs.UniversalIR.Surface as U
open import LogOS.Packs.UniversalIR.Agreement as UAgree
```

For a bundled entrypoint, use `LogOS.Packs.UniversalIR.Surface` (or the umbrella pack `LogOS.Packs.Universality.Surface`).
If you want the bundled pack (UniversalIR + agreement + meta-language surfaces), import `LogOS.Packs.Universality.Surface`.
If you want the **meta-language refinement** only (scheme/process + functorial contracts),
import `LogOS.MetaLanguage.All`.
For the lightweight universality surface, import `LogOS.Packs.Universality.Core`
(core code + `CoreScheme` only).

Examples are intentionally separated from the core surface:

```text
open import LogOS.Packs.UniversalIR.Examples as UEx
```

Notable example:
- `LogOS/Domain/UniversalIR/Examples/LambdaShowcase.agda` — raw vs certified λ transpilation metrics plus a five-paradigm output snapshot.

## A good first stop

- `LogOS/Domain/UniversalIR/README.md` (map of submodules)
- `LogOS/Domain/UniversalIR/Walkthrough.lagda.md` (worked narrative with examples)

## Proof status (honest summary)

- **Universal substrate present:** Minsky is included in `UCode` with a total stepper.
- **Agreement theorem (PA fragment):** `PATask` is transpiled to five paradigms and
  proved to agree (`LogOS/Domain/UniversalIR/Theorems.agda`, re-exported by
  `LogOS/Packs/UniversalIR/Agreement.agda`).
- **Quantum circuits are explicit:** syntax + stepper + checked gate-level examples
  (`Core/QuantumCircuit` and `Examples/QuantumCircuit`).
- **Quantum processes are kernel-aligned:** oracle/circuit observations are now
  derived from the kernel observation kits, so the code/boundary linkage is
  provided by `KernelUniversalProcess` rather than bespoke wrappers.
- **Costs are two-axis:** work vs measurement are tracked separately via `QNat2`
  and propagated through the scheme layer (`LogOS/Domain/UniversalIR/Schemes.agda`).
- **Budget transport is first-class:** `ProcessHomCost` / `ProcessHomCostWithGrade`
  transport cost/exec preservation statements across representations (`LogOS/Computation/SchemeCategory.agda`).
- **Compiler correctness (explicit fuel):** `CompilerCorrectness` packages the
  per-paradigm “compile + run with budget” correctness statements.
- **Semantic center alignment:** `compiler-correct-observe` (in
  `LogOS/Domain/UniversalIR/CompilerCorrectness.agda`) gives a one‑line bridge
  from operational correctness (`runU`) to the IR observation center
  (`observe ∘ simulate`).
- **Bounded transpilation to circuits:** circuit transpilation is indexed by step bounds.
- **Non‑PA example:** factorial is implemented via the While route
  (`LogOS/Domain/UniversalIR/While/Theorems.agda`).

## Bibliography pointers (not exhaustive)

- A. M. Turing (1936), "On Computable Numbers, with an Application to the Entscheidungsproblem".
- A. Church (1936), "An Unsolvable Problem of Elementary Number Theory".
- S. C. Kleene (1936), "General Recursive Functions of Natural Numbers".
- M. L. Minsky (1967), "Computation: Finite and Infinite Machines".
- D. Deutsch (1985), "Quantum Theory, the Church-Turing Principle and the Universal Quantum Computer".
- M. A. Nielsen and I. L. Chuang (2000), "Quantum Computation and Quantum Information".

### One-line agreement theorem (PA fragment)

The production library includes a single aggregation lemma stating agreement
between all five `PATask` paradigms (Minsky/λ/EVM/Oracle/Circuit):

- `LogOS/Domain/UniversalIR/Theorems.agda` exposes `patask-paradigms-correct`
  (now a named record) and `patask-paradigms-runEq`.
- `patask-paradigms-runEq` phrases the same statement via the generic scheme
  equivalence alias `Sch.RunEq` (standard “same function” packaging).

### Upgrade: arbitrary tasks (UniversalIR code as the task language)

The natural “make this work for all schemes” step is: stop choosing a small
input language (like `PATask`) and instead treat the **UniversalIR code itself**
as the task language.

This is implemented in `LogOS/Domain/UniversalIR/ArbitraryTasks.agda`:

- `UCodeTask = Fuelled UCode` and `runUCodeTask : UCodeTask → ℕ`
- `MinskyTask = Fuelled MinskyCode` maps into `UCodeTask` via `UM`
  (`embedMinskyTask`) and agrees definitionally:
  `runMinskyTask≡runUCodeTask`

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
- **No omniscient deciders (diagonal barrier):**
  `LogOS/Theorems/Meta/Tarski.agda` (`undef-classical`) and
  `LogOS/Theorems/Meta/Assumptions/Diagonal.agda` (`noOmniscientDeciderC`).
- **No total oracles within a budget:** `LogOS/Theorems/Meta/BudgetedSeparationOutput.agda`
  (both ℕ-budgets and abstract budget predicates for graded kernels).

For convenience, the curated UniversalIR surface re-exports these under
`LogOS.Packs.UniversalIR.All.Guardrails`.

## Refinement: a polymorphic meta-language

Beyond “Universal IR”, the same codebase already supports a second reading of
universality: **`Scheme`/`Process` is a polymorphic, resource-aware meta-language
for computation**, and UniversalIR is one concrete, richly-instantiated model.

The refinement is packaged as:
- `LogOS/MetaLanguage/All.agda`

It exposes, in one place:
- **Scheme/Process semantics:** `LogOS/Computation/Scheme.agda` and
  `LogOS/Computation/SchemeCategory.agda`
- **Kernel-as-process bridge (canonical, no extra axioms):**
  `LogOS/Computation/KernelUniversalProcess.agda` (`ForKernel.decodeHom` and the graded variant)
- **Functorial “contract language” over signatures:**
  `LogOS/Free/ConstraintsOverSig.agda` (renaming + naturality:
  `rename∂`/`renameb`, `interp∂-rename`, `interpb-rename`)
- **Open-system wiring primitives at the signature level:**
  `LogOS/Base/Ops/Boundary.agda` and `LogOS/Base/Ops/Cospan.agda` (bundled by `LogOS/Base/Signature.agda`)
