<!--
LogOS: an Agda research library for foundational logic system architecture.
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

Core: `LogOS/Domain/Universality/Core.agda`
- ToyUCode: sum type of codes (TuringCode, ChurchCode, ToyQuantumCode, ChainCode)
- stepToyU: one-step semantics for each branch
- simulateToy: iterate stepToyU n times

Adapters: `LogOS/Domain/Universality/Adapters.agda`
- Re-export the bridge tooling: canonical adapter, Rice/BodyEq transports,
  Flow universality lemmas, and the toy-spectrum complexity/separation scaffolding.

Physics-of-information packs (Landauer / DPI / measurement-capacity) live in:
- `LogOS/Domain/Complexity/LCUToLandauer.agda`
- `LogOS/Domain/Complexity/SecondLaw.agda`
- `LogOS/Domain/Complexity/MeasurementCapacity.agda`
- `LogOS/Domain/Complexity/NonUnitaryCapacity.agda`
- `LogOS/Domain/Complexity/DataProcessingInequality.agda`

Curated surface: `LogOS/Packs/Universality/Core.agda`
- Recommended stable import surface (no demos).

This directory intentionally does not provide a large `All` umbrella module; import
`Core`/`Adapters` directly when you want the minimal ingredients.

Making it executable
- The stepToyU function is total and simulateToy executes a code for n steps.
- These simple models are intentionally minimal, but already demonstrate the
  unifying pattern: each paradigm is a code + step pair.

Hooking into Kernel
- `LogOS/Domain/Universality/Kernel.agda` provides a concrete Kernel instance `UK` with
  `Code = ToyUCode` and `Guard = stepToyU`, so the guarded reflection layer talks about
  the same stepper executable via `simulateToy`.
Same PA computation across schemes
- See `LogOS/Domain/Universality/PAExample.agda`:
  - `encodeT/encodeC/encodeQ/encodeB` map the same input `n` to each scheme.
  - `simulateToy n (encodeX n)` reduces to the same conceptual result: “decrement-to-zero”
    while advancing the program counter (Turing/Chain) or shrinking size/gates (Church/Quantum).
