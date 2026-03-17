<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Application sketches (shape guides)

```agda
{-# OPTIONS --safe #-}
module docs.Interpretations.Applications.Application_Sketches where

import LogOS.API.LT
```

This note collapses the application shape guides into one page. These are
reader-facing generic patterns, not architectural capstones.

Practical companion:
`docs/Patterns/HowTo/HowTo_Practical_Architecture_Tips.lagda.md`.

Shared-boundary realisations pattern
------------------------------------

- Start from the generic shared-boundary / many-realisations surface.
- Choose one distributed semantics ledger (`DependentLocalSemantics`) and package
  each realisation over that boundary.
- Add law ports and port stacks only when the mathematical story really needs
  the extra doctrine.
- Keep domain readings downstream. The primitive pattern is the typed base layer,
  not any particular external interpretation.

Pointers (shared-boundary pattern)

- `LogOS/Ports/Realisations/DependentStack.agda`
- `LogOS/Ports/Realisations/Architecture.agda`
- `LogOS/Ports/PhysicalSemantics/Core.agda`
- `LogOS/Ports/PhysicalTransformers.agda`
- `LogOS/Ports/RestrictedProduct.agda`

Flagship stacked-transformer universality architecture
------------------------------------------------------

- Start from one canonical adapter surface and one universal kernel ledger.
- Read the pack through the two existing `Flow + Budget` stacked port
  categories: the observational `LOG` basis and the architecture-first
  `LOGᴳʳ` basis.
- Treat tasks and measured agreement as thin instantiations of one generic
  measured-encoding family.
- Keep cost/budget structure explicit as a port layer rather than rederiving
  it app-locally.
- Do not add a new app façade when the app is only one layered slice; use a
  dedicated façade only when one canonical lower-rung object really drives
  several downstream readings.

Pointers (Universality)

- `LogOS/Apps/Universality/All.agda`
- `LogOS/Apps/Universality/Architecture.agda`
- `LogOS/Apps/Universality/Stack.agda`
- `LogOS/Apps/Universality/Agreement/Universal.agda`
- `LogOS/Ports/Universality/FlowBudget2Cat.agda`
- `LogOS/Ports/Universality/ArchitectureFlowBudget2Cat.agda`
- `LogOS/Ports/Universality/Core.agda`
- `LogOS/Ports/Universality/Task.agda`
- `LogOS/Adapters/Universality/Lambda.agda`
- `LogOS/Adapters/Universality/Minsky.agda`
- `LogOS/Adapters/Universality/EVM.agda`
- `LogOS/Adapters/Universality/PreQuantum.agda`
- `LogOS/Adapters/Universality/PreQuantumCircuit.agda`

What is not claimed
-------------------

- no completeness theorem for the shared-boundary realisations pattern from this
  note alone;
- no claim that the current universality adapters exhaust the intended pack
  space;
- no claim that these sketches are part of the LT core rather than downstream
  application guidance.
