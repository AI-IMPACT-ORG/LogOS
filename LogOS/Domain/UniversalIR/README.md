<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

Universal IR (Standard Library)
===============================

This directory is a small, self-contained “universal translation machine” library.
In LogOS terms, it is the executable universal-logic spine for the IR story:
multiple concrete backends compile into a common carrier (`UCode`), can be executed
via the shared small-step interpreter (`stepU`/`simulate`) for a chosen step budget,
and are then lowered to a
canonical IR branch and decoded to an answer.
For a kernel-aligned view, `LogOS/Domain/UniversalIR/ObservedKernel.agda` packages
an observation space as a step-homomorphism (an `ObsKit`). This yields a kernel
over `UCode` whose boundary evolution is well-defined for the chosen observation.
The canonical `observe : UCode → ℕ` remains the semantic center for agreement,
but it is not a step-homomorphism in general (so it is kept as an observation,
not as a kernel boundary step). For other boundaries, use `UProcessAt`/`UProcessObs`
in `LogOS/Domain/UniversalIR/Schemes.agda`.

The recommended, representation-agnostic execution interface is **scheme-indexed**:
use `ScaleOps` to interpret a scale/grade as a step budget and run via `Sch.run≤`
or `Cat.run≤` (see `LogOS/Domain/UniversalIR/Schemes.agda`). The schedule-based
`Sch.run` (where the schedule is the scheme’s `fuel`) remains for literature
alignment and as a convenience wrapper.

Backends
--------
- `LogOS/Domain/UniversalIR/Languages/Minsky.agda` — 4-register Minsky machine (Turing complete)
- `LogOS/Domain/UniversalIR/Languages/Lambda.agda` — untyped λ-calculus (normal-order β-step; Church numerals)
- `LogOS/Domain/UniversalIR/Languages/Ethereum.agda` — EVM-like unbounded stack/memory machine (jumps + memory; `MUL`)
- `LogOS/Domain/UniversalIR/Languages/QuantumOracle.agda` — minimal oracle-with-classical-control model (oracle tape / measurement instruction)
- `LogOS/Domain/UniversalIR/Languages/QuantumCircuit.agda` — explicit basis-state circuit syntax (X/CNOT/TOFF + deterministic measurement)
- `LogOS/Domain/UniversalIR/Core/QuantumCircuitAmp.agda` — amplitude-level circuit semantics (abstract scalars, Born-style distribution)
  with explicit measurement axioms (`QMeasureLaws`) for normalization/coherence
- Boundary choices are explicit for the quantum cores: `boundaryWires` (wires) and
  `boundaryRegs` (register projections), plus `MeasurementObs` for amplitude-level observation.

The concrete small-step semantics for each paradigm live in `LogOS/Domain/UniversalIR/Core.agda`.

Entry points
------------
- **Recommended stable surface:** `LogOS/Packs/UniversalIR/Core.agda` (curated, no demos)
- **Pack skeleton (Assumptions/Claim/Pack/mkPack):** `LogOS/Domain/UniversalIR/Pack.agda`
  (curated re-export: `LogOS/Packs/UniversalIR/Pack.agda`)
- `LogOS/Domain/UniversalIR/Std.agda` — tiny shared lemma pack (“mini stdlib”)
- `LogOS/Domain/UniversalIR/ObservedKernel.agda` — observed-kernel view (`KernelObsKit` for
  observation-only, `ObsKit` for step-homomorphic boundaries; includes `CodeObsKit` and a
  λ-branch projection `LambdaObsKit`). Each `ObsKit` yields a canonical boundary
  port via `ObservedKernel.Ports`.
- `LogOS/Packs/UniversalIR/Kernel.agda` — curated kernel access plus pack-level
  port defaults for common observation kits (`ObservedPorts`).
- `LogOS/Computation/Scheme.agda` — shared scheme interface (`run≤`, fuel-free `ComputesTo`/`ComputesWithin`)
- `LogOS/Computation/Tasks.agda` — generic “arbitrary tasks” layer for any `Process`/`Scheme`
  (finite/graded execution + strict/lax transport lemmas)
- `LogOS/Computation/KernelBoundaryTasks.agda` — kernel-induced lax task transport
  (raw boundary steps vs Flow-saturated boundary steps)
- `LogOS/Domain/UniversalIR/Walkthrough.lagda.md` — narrative walkthrough
- `LogOS/Domain/UniversalIR/ArbitraryTasks.agda` — treat `UCode` itself as a task language (Minsky as an example)
- `LogOS/Domain/UniversalIR/TasksToUProcess.agda` — transport raw code tasks along the canonical backend→UProcess morphisms
- `LogOS/Domain/UniversalIR/Examples/Addition.agda` — addition across all backends
- `LogOS/Domain/UniversalIR/Examples/Multiplication.agda` — multiplication across all backends
- `LogOS/Domain/UniversalIR/Examples/Convincing.agda` — theorem-backed agreement (Minsky ≡ EVM) for all tasks
- `LogOS/Domain/UniversalIR/Examples/LambdaShowcase.agda` — raw vs certified λ compilation metrics + five-paradigm output snapshot
- `LogOS/Domain/UniversalIR/Theorems.agda` — non-trivial correctness lemmas (e.g. certified Minsky multiplication)
- `LogOS/Domain/UniversalIR/While/Language.agda` — small 2-variable While language (`whileNZ`, `mulAB`, factorial)
- `LogOS/Domain/UniversalIR/While/Theorems.agda` — theorem-backed factorial correctness (Minsky, all inputs)
- `LogOS/Domain/UniversalIR/While/Examples/Factorial.agda` — non-trivial concrete agreement (factorial 5 = 120)
- `LogOS/Domain/UniversalIR/While/Examples/CertifiedTranspile.agda` — certified decompile/transpile + “decompile twice”

Proof status
------------
- **Proved for all inputs (in this PA fragment):** Minsky (`minsky-correct`), λ-calculus (`lambda-correct`), EVM (`ethereum-correct`), Oracle (`oracle-correct`), and Circuit (`circuit-correct`) in `LogOS/Domain/UniversalIR/Theorems.agda`
- **Skeptic-facing corollary:** `LogOS/Domain/UniversalIR/Examples/Convincing.agda` derives Minsky ≡ EVM agreement for all `PATask`
- **λ backend note:** `LogOS.Domain.UniversalIR.Languages.Lambda.compileBrand` emits a Church numeral of `eval` (certified by construction); the raw β-reduction compiler remains as `LogOS.Domain.UniversalIR.Languages.Lambda.compileRawBrand` for inspection
- **While factorial:** Minsky is proved for all `n` (`LogOS/Domain/UniversalIR/While/Theorems.agda`); EVM is shown on `n = 5` by normalization (`LogOS/Domain/UniversalIR/While/Examples/Factorial.agda`)

Extending
---------
To add a new backend, implement a compiler into a brand code and provide an injection
into `UCode` as a `Backend` (`LogOS/Domain/UniversalIR/Backend.agda`). Then use
`Backend.exec`/`Backend.toIRAt`/`Backend.decodeAt` to execute it with a chosen step budget.
For other observation spaces, use `UProcessAt`/`UProcessObs` and the `*ProcessAt`
constructors in `LogOS/Domain/UniversalIR/Schemes.agda` to keep machine processes
and universal-process factoring aligned.

For paradigm-independent semantics (“machines as schemes”), use the fuel-free predicates
on `Scheme` (`LogOS/Computation/Scheme.agda`), such as `ComputesTo` / `ComputesWithin`,
and the **grade-indexed** runner `run≤` parameterized by `ScaleOps`.
The induced equivalence `ObsEq` is the library’s “same computation” notion.

Algorithm vs implementation
---------------------------
- **Algorithm**: a machine-independent specification (`Sch.Algorithm`).
- **Implementation**: a particular scheme plus correctness (`Sch.ImplementsRun` / `Sch.ImplementsRel`).
- In this directory, `PATask`’s evaluator `eval` is packaged as an algorithm (`PAAlg`)
  and multiple schemes implement it (`*-implements-PA` in `LogOS/Domain/UniversalIR/Theorems.agda`).

Guardrails (meta theorems)
--------------------------
- Representation invariance for grade-indexed execution: `run≤-map` / `run≤-meaning-comm` in `LogOS/Computation/SchemeCategory.agda`.
- No total observers/deciders under diagonalization:
  `LogOS/Theorems/Meta/SpectralSeparationOutput.agda` (event-horizon witnesses),
  `LogOS/Theorems/Meta/Tarski.agda` (`undef-classical`), and
  `LogOS/Theorems/Meta/Assumptions/Diagonal.agda` (`noOmniscientDeciderC`).
- No total certificate oracle within any fixed (or code-indexed) budget:
  `LogOS/Theorems/Meta/BudgetedSeparationOutput.agda` (ℕ budgets) and
  `LogOS/Theorems/Meta/SpectralSeparationOutput.agda` (`GeneralB.WitnessCostB` for abstract budgets).

Naming note (Quantum)
---------------------
- Use `LogOS/Domain/UniversalIR/Languages/QuantumOracle.agda` and/or `LogOS/Domain/UniversalIR/Languages/QuantumCircuit.agda` explicitly.
- No `Quantum` alias module is provided; prefer the explicit modules above.
