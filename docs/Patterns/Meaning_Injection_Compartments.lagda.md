<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Design decision: Meaning injection compartments

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Meaning_Injection_Compartments where

import LogOS.API.LT
```

Meaning injection points (explicit)
-----------------------------------

- `View` fixes observation and therefore refinement (pullback).
- `Kernel` packages the observation as `decode`.
- Ports add extra obligations without changing refinement.

Compartment rules
-----------------

- Meaning changes must be explicit and isolated.
- Non-pointwise meaning changes must be quarantined.
- Bridges must declare their contracts.

Pointers
--------

- `LogOS/LT/View.agda`
- `LogOS/LT/Kernel.agda`
- `LogOS/Ports/Bridges/**`
- `LogOS/Ports/Quarantine/**`
