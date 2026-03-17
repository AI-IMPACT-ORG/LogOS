<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Architecture (intended) {#architecture-intended}

Dependency layering for the library, organised around *logical transformers*.

```agda
{-# OPTIONS --safe #-}
module docs.Core.Architecture.Diagram where

import LogOS.API.LT
```

Import direction in this diagram is explicit:
- if there is an arrow from A to B, then code in A may import code in B;
- therefore arrows always point from higher layers to lower layers.

Canonical layer order is generated from `scripts/lib/layers.sh` into:
- `docs/Generated/Architecture_Layer_Order.md`

```text
┌──────────────────────────────────────────────────────────────┐
│ Curated API surface (`API`, rank 7)                          │
│ `LogOS/API/**`                                               │
└───────────────────────────┬──────────────────────────────────┘
                            │
                            ▼
┌──────────────────────────────────────────────────────────────┐
│ Applications (`Apps`, rank 6)                                │
│ `LogOS/Apps/**`                                              │
└───────────────────────────┬──────────────────────────────────┘
                            │
                            ▼
┌──────────────────────────────────────────────────────────────┐
│ Adapters (`Adapters`, rank 5)                                │
│ `LogOS/Adapters/**`                                           │
└───────────────────────────┬──────────────────────────────────┘
                            │
                            ▼
┌──────────────────────────────────────────────────────────────┐
│ Ports (`Ports`, rank 4)                                      │
│ `LogOS/Ports/**`                                              │
└───────────────────────────┬──────────────────────────────────┘
                            │
                            ▼
┌──────────────────────────────────────────────────────────────┐
│ Logical transformers (`LT`, rank 3)                          │
│ kernel + hom + LOG + displayed port calculus                 │
│ `LogOS/LT/**`                                                 │
└───────────────────────────┬──────────────────────────────────┘
                            │
                            ▼
┌──────────────────────────────────────────────────────────────┐
│ Syntax (`Syntax`, rank 2)                                    │
│ `LogOS/Syntax/**`                                              │
└───────────────────────────┬──────────────────────────────────┘
                            │
                            ▼
┌──────────────────────────────────────────────────────────────┐
│ Prelude (`Prelude`, rank 1)                                  │
│ `LogOS/Prelude.agda`                                           │
└───────────────────────────┬──────────────────────────────────┘
                            │
                            ▼
┌──────────────────────────────────────────────────────────────┐
│ Host (`Host`, rank 0)                                        │
│ `LogOS/Host/**`                                               │
│ (the only place touching `Agda.Primitive` / builtins)         │
└──────────────────────────────────────────────────────────────┘
```

Extra enforcement notes:

- `layer-order-check` enforces only the *coarse* layering above.
- The curated API is intentionally stricter: `api-purity-check` forbids `LogOS/API/**` from importing
  from `LogOS/Apps/**` or `LogOS/Adapters/**`. Apps are domain packs; the core API is boundary/port/kernel-first.

Guiding rule: the core defines *what a logical transformer is*; everything else should be expressed as a
translation/adaptation/application of that core.

Port naming convention (capability-first):
- a port module exports a single record value (e.g. `port2Cat`/`stack2Cat`) and then `open … public` to expose the
  uniform surface: `Displayed`, `WithPort`, `forget`, `stack`, and `port` (capability).
- projections are structural: use `PortStack.baseObj` / `PortStack.baseHom` for the underlying 1-cell,
  and `PortStack.getObj` / `PortStack.getHom` with the exported `port` capability for the payload.
  Avoid bespoke `…KernelOf`/`…PortOf` wrappers unless they add non-trivial behaviour.

Hexagonal discipline: `LogOS/Ports/**` defines interfaces; `LogOS/Adapters/**` implements them (adapters may depend on ports,
never the other way around).

Design note: the “ports as displayed layers” decision is documented in:

- `docs/Patterns/Ports_As_Displayed.lagda.md`
