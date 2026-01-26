<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

Computational Universality in One Language
=========================================

We present four paradigms as different instantiations of one core, with different
“regulators” (step interpretation):

- Turing/Minsky (register machine)
- Church (λ-calculus)
- Quantum (gates/circuits)
- Blockchain (EVM-like, gas-based)

Interpretation (analogy):
this README references “physics of information” vocabulary as motivation; any formal content is only what is stated in the cited Agda modules and their explicit assumptions.

Core: `LogOS/Domain/Universality/Core.agda`
- CoreUCode: sum type of codes (TuringCode, ChurchCode, CoreQuantumCode, ChainCode)
- stepCoreU: one-step semantics for each branch
- simulateCoreU: iterate stepCoreU n times

Umbrella surface: `LogOS/Domain/Universality/All.agda`
- Unified surface: bridge tooling (Rice/BodyEq transports), Flow universality
  lemmas, and the core-spectrum complexity/separation scaffolding, plus scheme
  presentation and lemma bundles.

Physics-of-information packs (Landauer / DPI / measurement-capacity) live in:
- `LogOS/Domain/Complexity/LCUToLandauer.agda`
- `LogOS/Domain/Complexity/SecondLaw.agda`
- `LogOS/Domain/Complexity/MeasurementCapacity.agda` (record `NonUnitaryCapacity`)
- `LogOS/Domain/Complexity/DataProcessingInequality.agda`

Curated surface: `LogOS/Packs/Universality/Core.agda`
- Recommended stable import surface (no demos). It re-exports only the core
  executable code plus the `CoreScheme` wrapper and the canonical port view
  (`Core.Ports`).

`LogOS/Domain/Universality/All.agda` exists as a convenience umbrella; when you want
the minimal ingredients, import `LogOS/Domain/Universality/Core.agda` directly (and
only the bridge modules you need).

Executable universal logic
- The stepCoreU function is total and simulateCoreU (alias: execCoreU) executes
  a code for n steps.
- These simple models are intentionally minimal, but already demonstrate the
  unifying pattern: each paradigm is a code + step pair.

Hooking into Kernel
- `LogOS/Domain/Universality/Kernel.agda` provides a concrete Kernel instance `UK` with
  `Code = CoreUCode` and `Guard = stepCoreU`, so the guarded reflection layer talks about
  the same stepper executable via `simulateCoreU`.
 - `LogOS/Domain/Universality/KernelRich.agda` refines the **boundary preorder** to
   observational equality (`observeCore`) and uses canonicalization as `Flow`.
   Its H-tier truth is intentionally vacuous, so canonical ports are best read as
   structural wiring unless you add separate non-vacuity/meaningfulness assumptions.
Same PA computation across schemes
- See `LogOS/Domain/Universality/PAExample.agda`:
  - `encodeT/encodeC/encodeQ/encodeB` map the same input `n` to each scheme.
  - `simulateCoreU n (encodeX n)` reduces to the same conceptual result: “decrement-to-zero”
    while advancing the program counter (Turing/Chain) or shrinking size/gates (Church/Quantum).
