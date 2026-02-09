<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

A Universality-style Core (Four Paradigms, One Stepper)
=======================================================

We present four paradigms as different instantiations of one core, with different
“regulators” (step interpretation):

- Turing/Minsky (register machine)
- Church (λ-calculus)
- Quantum (gates/circuits)
- Blockchain (EVM-like, gas-based)

Interpretation (analogy):
this README references “physics of information” vocabulary as motivation; any formal content is only what is stated in the cited Agda modules and their explicit assumptions.

Core: `LogOS/Universality/Core.agda`
- CoreUCode: sum type of codes (TuringCode, ChurchCode, CoreQuantumCode, ChainCode)
- stepCoreU: one-step semantics for each branch
- simulateCoreU: iterate stepCoreU n times

Umbrella surface: `LogOS/Universality/Surface.agda`
- Unified surface: bridge tooling (Rice/BodyEq transports), Flow universality
  lemmas, and the core-spectrum complexity/separation scaffolding, plus scheme
  presentation and lemma bundles.

Physics-of-information packs (Landauer / DPI / measurement-capacity) live in:
- `LogOS/Complexity/LCUToLandauer.agda`
- `LogOS/Complexity/SecondLaw.agda`
- `LogOS/Complexity/MeasurementCapacity.agda` (record `NonUnitaryCapacity`)
- `LogOS/Complexity/DataProcessingInequality.agda`

Curated surface: `LogOS/Packs/Universality/Core.agda`
- Recommended stable import surface (no demos). It re-exports only the core
  executable code plus the `CoreScheme` wrapper and the canonical port view
  (`Core.Ports`).

Index module: `LogOS/Universality/All.agda`
- Lightweight, namespaced navigation surface (discoverability only).

`LogOS/Universality/Surface.agda` exists as a convenience umbrella; when you want
the minimal ingredients, import `LogOS/Universality/Core.agda` directly (and
only the bridge modules you need).

Executable stepper core
- The stepCoreU function is total and simulateCoreU (alias: execCoreU) executes
  a code for n steps.
- These simple models are intentionally minimal, but already demonstrate the
  unifying pattern: each paradigm is a code + step pair.

Hooking into Kernel
- `LogOS/Universality/Kernel.agda` provides a concrete Kernel instance `UK` with
  `Code = CoreUCode` and `Guard = stepCoreU`, so the guarded reflection layer talks about
  the same stepper executable via `simulateCoreU`.
 - `LogOS/Universality/KernelRich.agda` refines the **boundary preorder** to
   observational equality (`observeCore`) and uses canonicalization as `Flow`.
   Its H-tier truth is intentionally vacuous, so canonical ports are best read as
   structural wiring unless you add separate non-vacuity/meaningfulness assumptions.
Same PA computation across schemes
- See `LogOS/Universality/PAExample.agda`:
  - `encodeT/encodeC/encodeQ/encodeB` map the same input `n` to each scheme.
  - `simulateCoreU n (encodeX n)` reduces to the same conceptual result: “decrement-to-zero”
    while advancing the program counter (Turing/Chain) or shrinking size/gates (Church/Quantum).
