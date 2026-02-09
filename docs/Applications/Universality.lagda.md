<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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

Trust level: **stable** (lock surface: `LogOS/Packs/Universality/Surface.agda`).

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`.

The goal is to present computation *inside LogOS* as a **universal process
model**: multiple internal languages (Minsky, untyped λ-calculus, quantum
oracle/circuit models, a small EVM-like language) share a single semantic center
and explicit translations.

Naming note (guardrail): “Minsky”, “λ”, “quantum”, “EVM-like” refer to internal
formal languages in `LogOS/UniversalIR/Languages/*`. Any alignment to
external systems is interpretive and must be justified by explicit adapters and
assumptions; the literal claims are only about the included semantics.

## Church–Turing / ECT / Deutsch (what is and isn’t claimed)

This repository intentionally separates:

- **CT (Church–Turing thesis)** as a literature thesis about the informal notion
  of “effective procedure” (not a theorem).
- **ECT (extended Church–Turing thesis)** as an efficiency-strengthening (also
  not a theorem, and known to be delicate once quantum models are admitted).
- **Deutsch’s Church–Turing principle** (often paraphrased as “every finitely
  realizable physical system can be simulated by a universal computing device”)
  as a *physical* principle (not a theorem of mathematics).

Interpretation (analogy): this is a literature crosswalk; any use of “physical”
language here is explanatory and does not constitute a proved claim about the
world.

What LogOS claims in this application is an **internal, interface-level**
statement that matches the “mechanisable ⇒ simulable” direction:

- A notion of **mechanisable observation** is packaged as an `ObsKit` in
  `LogOS/UniversalIR/ObservedKernel.agda`: an observation `observeU : UCode → Obs`
  equipped with a step-homomorphism law `observeU (stepU γ) ≡ obsStep (observeU γ)`.
- From any `ObsKit`, LogOS constructs an “observed kernel” (`ForObsKit.ObsKernel`)
  and a canonical simulation/transport map `decodeHom` via the general
  kernel-as-process bridge `LogOS/Computation/KernelUniversalProcess.agda`.

In other words: the library can prove simulation theorems **conditional on a
precise mechanisability interface**; any claim that “physics supplies such an
interface” must be made explicitly as an assumption or as a separately
mechanised physics model.

## Curated surfaces (stable)

- Universal IR core: `LogOS/Packs/UniversalIR/Core.agda`
- Agreement theorem (paper-facing): `LogOS/Packs/UniversalIR/Agreement.agda`
- Stable lock surface (IR + agreement + meta-language): `LogOS/Packs/Universality/Surface.agda`
- Meta-language refinement (schemes/processes): `LogOS/MetaLanguage/All.agda`
- Core universality surface (lightweight, minimal exports): `LogOS/Packs/Universality/Core.agda`
- Compiler-correctness packaging (compile + explicit fuel budgets):
  `LogOS/UniversalIR/CompilerCorrectness.agda`
- Kernel/port view for the core (boundary port + code port):
  `LogOS/Packs/Universality/Core.agda` (module `Ports`)
- Kernel/port view for UniversalIR observation kits:
  `LogOS/Packs/UniversalIR/Kernel.agda` (module `ObservedPorts`)

Boundaries are explicit: the strong “all paradigms agree for all inputs”
claim (formal shape: `Sch.RunEq` for all programs) is *not* assumed; the library proves agreement for selected fragments and
examples, and exposes the machinery needed to extend it.

Two complementary universality surfaces live side by side:
- **UniversalIR** is the heavy, multi-paradigm IR with translations and agreement.
- **Universality (core)** is a small, total, executable universality sketch
  (`LogOS.Packs.Universality.Core`) intended for lightweight reasoning. It now
  re‑exports only `LogOS.Universality.Core`, with the scheme wrapper under
  `CoreScheme` to keep the surface tight. The kernel view refines the **boundary
  preorder** to observational equality (`observeCore`) and supplies a canonical
  representative map (`Flow = canonCore`). Its H-tier truth is intentionally
  vacuous, so canonical ports should be read as structural wiring unless you add
  separate non-vacuity/meaningfulness assumptions.

In the “scheme” view, the library defines a canonical notion of **what computation is (in LogOS)**:
as a fuel-free computation relation (`Sch.Scheme.ComputesTo`, i.e. “there exists a run to an `≡`‑fixed point”)
and its induced observational equality (`Sch.ObsEq`), plus an explicit operational budget
layer (`Sch.ExecWithin` / `Sch.ReachesWithin`), rather than as a particular machine.
For quotient-friendly “stability up to observation”, use the preorder/closure-stable variants
(`halts`, `ComputesToObs`, `StabilizesTo`) in `LogOS/Computation/Scheme.agda`.

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
   full `Sch.RunEq` agreement of paradigms for arbitrary computation would require
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
  transport cost/budget claims, use `ProcessHomCost`
  from `LogOS/Computation/SchemeCategory.agda`.

## The core idea

- Each paradigm is a small-step semantics on a concrete code type.
- A single unified carrier (`UCode`) packages those codes.
- “Same computation” means: transpile/decompile/translate between paradigms and
  prove agreement via the common observation function `observe : UCode → ℕ`
  (defined as `decode ∘ lowerToIR` in `LogOS/UniversalIR/IR.agda`).
  For a kernel-aligned observation space, use `ObsKit` in
  `LogOS/UniversalIR/ObservedKernel.agda`: it packages any observation
  `observeU : UCode → Obs` that commutes with `stepU` (a true step homomorphism).
  If you want a different output space in the scheme view, use `UProcessAt` or
  `UProcessObs` from `LogOS/UniversalIR/Schemes.agda`, plus the `*ProcessAt`
  constructors (e.g., `MinskyProcessAt`) for machine-level schemes.

The diagram the code enforces (via `Process`/`Interface` and `ProcessHom`) is:

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

Input ──Interface.compile──▶ state ──Step^(steps(budget g))──▶ state ──lowerToIR──▶ state ──decode──▶ ℕ
           │                         (scheme index g)             │
           └────────────────── ProcessHom ────────────┘
```

`ProcessHom` is the explicit semantic transport. If you also want cost/budget
claims to be preserved by translation, use `ProcessHomCost`.

## Where the code lives

- Universal IR + languages + semantics:
  - `LogOS/UniversalIR/*`
  - The curated, stable surface: `LogOS/Packs/UniversalIR/Core.agda`
- “Arbitrary tasks” (treat UniversalIR code as the task language):
  - `LogOS/UniversalIR/ArbitraryTasks.agda`
- Observed-kernel view (step-homomorphic observation kits):
  - `LogOS/UniversalIR/ObservedKernel.agda`
  - Canonical port view for any observation kit:
    `LogOS/UniversalIR/ObservedKernel.agda` (module `Ports`)
  - Pack-level defaults for common kits:
    `LogOS/Packs/UniversalIR/Kernel.agda` (module `ObservedPorts`)
- Pack skeleton (Assumptions/Claim/Pack/mkPack) for the “same computation, many
  representations” claim:
  - `LogOS/UniversalIR/Pack.agda`
  - Curated re-export: `LogOS/Packs/UniversalIR/Pack.agda`
- Agreement theorem (paper surface):
  - `LogOS/Packs/UniversalIR/Agreement.agda`
- Compiler correctness pack (end-to-end with explicit fuel):
  - `LogOS/UniversalIR/CompilerCorrectness.agda`
- Paradigms (examples):
  - Minsky machine: `LogOS/UniversalIR/Languages/Minsky.agda`
  - Untyped λ-calculus: `LogOS/UniversalIR/Languages/Lambda.agda`
  - EVM-like machine: `LogOS/UniversalIR/Languages/Ethereum.agda`
  - Quantum (two presentations):
    - oracle-with-classical-control: `LogOS/UniversalIR/Languages/QuantumOracle.agda`
    - explicit circuits: `LogOS/UniversalIR/Languages/QuantumCircuit.agda`
  - Tiny executable circuit sanity checks:
    - `LogOS/UniversalIR/Examples/QuantumCircuit.agda`
- “Universal computation as a process” (choices + morphisms):
  - `LogOS/Computation/SchemeCategory.agda`
  - `LogOS/UniversalIR/Schemes.agda`
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
- `LogOS/UniversalIR/Examples/LambdaShowcase.agda` — raw vs certified λ transpilation metrics plus a five-paradigm output snapshot.

## A good first stop

- `LogOS/UniversalIR/README.md` (map of submodules)
- `LogOS/UniversalIR/Walkthrough.lagda.md` (worked narrative with examples)

## Proof status (honest summary)

- **Universal substrate present:** Minsky is included in `UCode` with a total stepper.
- **Agreement theorem (PA fragment):** `PATask` is transpiled to five paradigms and
  proved to agree (`LogOS/UniversalIR/Theorems.agda`, re-exported by
  `LogOS/Packs/UniversalIR/Agreement.agda`).
- **Quantum circuits are explicit:** syntax + stepper + checked gate-level examples
  (`LogOS/UniversalIR/Core/QuantumCircuit.agda` and `LogOS/UniversalIR/Examples/QuantumCircuit.agda`).
- **Quantum processes are kernel-aligned:** oracle/circuit observations are now
  derived from the kernel observation kits, so the code/boundary linkage is
  provided by `KernelUniversalProcess` rather than bespoke wrappers.
- **Costs are two-axis:** work vs measurement are tracked separately via `QNat2`
  and propagated through the scheme layer (`LogOS/UniversalIR/Schemes.agda`).
- **Budget transport is first-class:** `ProcessHomCost`
  transport cost/exec preservation statements across representations (`LogOS/Computation/SchemeCategory.agda`).
- **Compiler correctness (canonical surface):** `CompilerCorrectness` packages
  both the fuel-indexed `PATask` compiler theorems and the expression-language
  `PAExprTask` compiler theorems.
- **Semantic center alignment:** `compiler-correct-observe` (in
  `LogOS/UniversalIR/CompilerCorrectness.agda`) gives a one‑line bridge
  from operational correctness (`runU`) to the IR observation center
  (`observe ∘ simulate`).
- **Bounded transpilation to circuits:** circuit transpilation is indexed by step bounds.
- **Non‑PA example:** factorial is implemented via the While route
  (`LogOS/UniversalIR/While/Theorems.agda`).

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

- `LogOS/UniversalIR/Theorems.agda` exposes `patask-paradigms-correct`
  (now a named record) and `patask-paradigms-runEq`.
- `patask-paradigms-runEq` phrases the same statement via the generic scheme
  equivalence alias `Sch.RunEq` (standard “same function” packaging).

### Upgrade: arbitrary tasks (UniversalIR code as the task language)

The natural “make this work for all schemes” step is: stop choosing a small
input language (like `PATask`) and instead treat the **UniversalIR code itself**
as the task language.

This is implemented in `LogOS/UniversalIR/ArbitraryTasks.agda`:

- `UCodeTask = Fuelled UCode` and `runUCodeTask : UCodeTask → ℕ`
- `MinskyTask = Fuelled MinskyCode` maps into `UCodeTask` via `UM`
  (`embedMinskyTask`) and agrees by propositional equality (in fact `refl` after unfolding):
  `runMinskyTask≡runUCodeTask`

### Checked example: measurement cost axis

These are small executable examples (not universality theorems) showing the
second cost component is charged by measurement primitives:

- `LogOS/UniversalIR/Examples/QuantumCircuit.agda`: `qMeasure-cost`
- `LogOS/UniversalIR/Examples/QuantumOracle.agda`: `qMeasure-cost`

## Guardrails (CS-style theorems)

The universality story is guarded by three generic theorems that do not depend
on any particular paradigm:

- **Representation invariance:** `LogOS/Computation/SchemeCategory.agda`
  (`run≤-map`, `run≤-meaning-comm`).
- **Axis-independence (ScaleOps):** `LogOS/Computation/SchemeCategory.agda`
  (`Semantics.Exec≤-stepsEq`), with a concrete `QNat2` specialization
  `run≤ᵁ-budget₂≡work` in `LogOS/UniversalIR/Schemes.agda`.
- **Semantics is functorial (category façade):** `LogOS/Computation/SchemeCategory.agda`
  (`ProcessCategory`, `Semantics`).
- **Relational ↔ schedule semantics bridge:** `LogOS/Computation/Scheme.agda`
  (`FuelHalts`, `Bridge.RunEq→ObsEq`, `Bridge.ObsEq→RunEq`).
- **No omniscient deciders (diagonal barrier):**
  `LogOS/Theorems/Meta/Tarski.agda` (`undef-classical`) and
  `LogOS/Theorems/Meta/Assumptions/Diagonal.agda` (`noOmniscientDeciderC`).
- **No total oracles within a budget:** `LogOS/Theorems/Meta/BudgetedSeparationOutput.agda`
  (both ℕ-budgets and abstract budget predicates for graded kernels).

Optional convenience surface:

```agda
open import LogOS.Packs.UniversalIR.Guardrails
```

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
  `LogOS/Minimal/ConstraintsOverSig.agda` (renaming + naturality:
  `rename∂`/`renameb`, `interp∂-rename`, `interpb-rename`)
- **Open-system wiring primitives at the signature level:**
  `LogOS/Base/Ops/Boundary.agda` and `LogOS/Base/Ops/Cospan.agda` (bundled by `LogOS/Base/Signature.agda`)
