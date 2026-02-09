<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Deep Dive — API Surfaces (Recommended Imports)

```agda
{-# OPTIONS --safe #-}
module docs.DeepDive.API_Surfaces where

-- This document is an executable import guide: it pins the intended “surface”
-- modules and gives copy/paste recipes.

import LogOS.API.Foundation
import LogOS.API.Kernel
import LogOS.API.PortsAdapters
import LogOS.API.Architecture
import LogOS.API.Minimal
import LogOS.API.Assumptions
import LogOS.API.Strengthenings
import LogOS.API.Axioms
import LogOS.API.Views

-- Packs: publication-facing, curated entrypoints.
--
-- Note: large topic libraries live under `LogOS/*` (e.g. `LogOS/UniversalIR/*`),
-- and experimental domains are quarantined under `LogOS/Domain/*` (Opacity).
import LogOS.Packs.ZFC.Surface
import LogOS.Packs.InfoTheory.Surface
import LogOS.Packs.Opacity.Experimental.Surface
import LogOS.Packs.Complexity.Experimental.PvsNP.Public
import LogOS.Packs.Universality.Surface
import LogOS.Packs.Agents.Surface
```

This page is the “recommended imports” map. It is intentionally *opinionated*:
the goal is to make it hard to accidentally depend on internal modules.

Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
Claim/assumption discipline: `docs/Kernel/ClaimRegister.lagda.md`.

## Quick recipes

### Kernel authoring (minimal safe core)

If you are defining your own signature, prequantale adapter, and kernel instance:

```agda
open import LogOS.API.Minimal
```

Use this when you want the smallest `--safe` surface with no axioms.

### Port-first downstream work (presentations + interlingua)

If you want boundary I/O, satisfaction systems, ports, and adapters without
pulling kernel internals into scope:

```agda
open import LogOS.API.Architecture as Architecture
open Architecture.Downstream
```

If you explicitly want the “ports + adapters” umbrella (still kernel-light):

```agda
open import LogOS.API.PortsAdapters
```

### Curry–Howard–Lambek “single system” view (Kernel)

If you want the shared S/H/code shape together with the parameterised guarded tier:

```agda
open import LogOS.API.Kernel
```

### Optional strengthenings (upgrades, not the default)

If you want extra law bundles (e.g. ω-sup interfaces, μ-limit transport, or stronger
closure/adjunction laws):

```agda
open import LogOS.API.Strengthenings
```

If you want *axiom interfaces* (explicit strengthenings):

```agda
open import LogOS.API.Axioms
```

### Packs (publication-facing entrypoints)

If you want a curated application strand, import its pack surface:

```agda
open import LogOS.Packs.ZFC.Surface
open import LogOS.Packs.InfoTheory.Surface
open import LogOS.Packs.Universality.Surface
```

Experimental packs are explicitly marked:

```agda
open import LogOS.Packs.Opacity.Experimental.Surface
open import LogOS.Packs.Complexity.Experimental.PvsNP.Public
```

## Anti-recipes (what not to do)

- Do not import `LogOS.Domain.*` (quarantined experimental domains) from publication-facing docs; use pack surfaces.
- Prefer pack surfaces (`LogOS.Packs.*.Surface`) over topic-library modules (`LogOS/{ZFC,UniversalIR,…}/*`) unless you are intentionally working inside those libraries.
- Do not import `LogOS.Host.*` or `Agda.Builtin.*` directly: use `LogOS.Prelude` (enforced by CI).
- Prefer API surfaces (`LogOS.API.*`) and pack surfaces (`LogOS.Packs.*`) over deep internal modules.

## Naming conventions (All vs Surface vs Core)

This repo uses a small number of recurring “surface” patterns to keep imports predictable:

- **Topic libraries** (`LogOS/{ZFC,Universality,UniversalIR,Complexity,ObjectLogic,InfoTheory}`):
  - `All` (e.g. `LogOS/ZFC/All.agda`) = *index only* (discoverability): use `import ... as ...` + `module Foo = Fooₜ`; avoid `open import ... public`.
  - `Surface` (e.g. `LogOS/ZFC/Surface.agda`) = *navigation umbrella*: may `open import ... public` to provide a convenient, namespaced entrypoint for interactive exploration.
- **Curated packs** (`LogOS/Packs/*`):
  - `Core` (e.g. `LogOS/Packs/ZFC/Core.agda`) = minimal curated pack surface + the single source of truth for `packTrust`.
  - `All` (e.g. `LogOS/Packs/ZFC/All.agda`) = batteries-included umbrella (may re-export more), but must re-use `Core.packTrust`.
  - `Surface` (e.g. `LogOS/Packs/ZFC/Surface.agda`) = stable publication-facing import surface (kept clean by CI checks).

Guardrails enforce the most important parts of this discipline:
`scripts/topic_kernel_api_check.sh` (topic libs import kernel via `LogOS.API.Kernel*`) and
`scripts/topic_all_index_check.sh` (topic `All` stays index-only).
