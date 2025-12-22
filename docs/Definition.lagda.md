<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% LogOS (Agda) — Start Here (Architecture, Kernel I/O, Packs)

```agda
module docs.Definition where

-- Sync guard: these imports are the public surfaces this document describes.
-- If they drift, the docs build fails.
open import LogOS.API.Minimal
open import LogOS.Packs.ZFC.All as ZFC
open import LogOS.Models.Complexity.Core as Complexity
open import LogOS.Models.Universality.Core as Universality
open import LogOS.Models.UniversalIR.Core as UniversalIR
open import LogOS.Models.Opacity.Core as Opacity
open import LogOS.Models.Opacity.Applications.GRH as GRH
```

This file is the recommended entry point for new users of the published LogOS
library. It explains the architecture, the Kernel “I/O surface”, and how the
major application packs (ZFC, complexity, universality/IR, opacity; and GRH as
an application) hang together.

If you want the *research‑grade* “list of records and laws” definition, see:
`docs/Definition_Spec.lagda.md`.

Repository Map
--------------
At the top level:
- `LogOS/*` — the core logic and the Kernel interface (small, host‑minimal).
- `LogOS/Algebra/*` — small algebraic surfaces (e.g. braiding, graph surface).
- `LogOS/Domain/*` — application/domain developments (ZFC, GRH, Complexity, UniversalIR, …).
- `LogOS/Models/*` — recommended import surfaces for the major storylines.
- `LogOS/Packs/*` — “publication bundles” (currently ZFC, Universality).
- `docs/*` — narrative docs (this file + topic guides).
- `Tests/*` — regression aggregation for CI.

Hexagonal Architecture (Ports/Adapters)
---------------------------------------
The library uses a hexagonal (ports/adapters) structure:

- **Core (ports):** minimal interfaces and laws live under `LogOS/Minimal/*` and
  are combined as the `LogOS/Kernel` record.
- **Adapters:** canonical constructions, folds, and transport lemmas live under
  `LogOS/Kernel/*`, `LogOS/Theorems/*`, and `LogOS/Algebra/*`.
- **Domain packs:** ZFC / complexity / physics / GRH live under `LogOS/Domain/*`
  and depend only on the ports + adapters.

This keeps “what the logic *is*” separate from “how we *use* it”.

Host-Minimal Surface (Portability Claim)
----------------------------------------
To make “LogOS could be hosted elsewhere” precise, the repo enforces a tiny host
surface: only a short list of files may import `Agda.Builtin.*` / `Agda.Primitive`.
Everything else depends on these wrappers.

See `scripts/host_surface_check.sh` for the enforced allowlist:
- `Level.agda`
- `Data/Nat.agda`
- `Data/Bool.agda`
- `Data/List.agda`
- `Data/Maybe.agda`
- `Data/Relation/Binary/PropositionalEquality.agda`

Kernel in One Page
------------------
The Kernel is the *integrated* model interface: it combines (i) your signature,
(ii) constraint semantics (a boundary logic), (iii) a 3‑tier truth structure, and
(iv) a reflective code interface.

The key design choice is: **truth is local and regulatable**.
You do not assume a single static “global truth predicate”; instead you model a
local boundary logic and a closure step (`Flow`) that represents the
stabilization/communication of truth.

### The three tiers (S / H / G)
LogOS separates three levels of truth:

- **S (Strict / syntactic):** a formula language `Fml` and satisfaction `Sat_S`.
- **H (Homotypical / semantic):** satisfaction `Sat_H` for boundary constraints,
  plus an invariance/projector `Inv_H` (truth “up to invariance”).
- **G (Guarded / stabilized):** a guarded closure (`GTruth`) on boundary
  constraints whose step is `Flow`, plus a distinguished (preorder) fixed point `Th*`
  (global stable truth).
  With optional antisymmetry (and, for ω-limit results, `OmegaCPO`/continuity structure),
  this upgrades to a genuine least-fixed-point story.

The coherence you must provide is explicit:
- `coh-LH` links S‑truth to H‑truth via a translation `TransH : Fml → Con∂`.
- `sat-coh` links world‑indexed H‑truth to boundary‑indexed H‑truth via `bnd`.

### Kernel I/O surface (the reflective boundary)
Every Kernel exposes a tiny “I/O” API that makes inference steps speak about
themselves *inside* the logic:

- `encode : Con∂ → Code`
- `decode : Code → Con∂` with `decode (encode c) ≡ c`
- `Guard : Code → Code` (one guarded step on code)
- `GTruth` exposes `Flow : Con∂ → Con∂` (closure step on constraints)
- the fundamental coherence law:
  - `decode (Guard γ) ≡ Flow (decode γ)`

Intuition:
- `Code` is the internal language of “programs / proofs / processes”.
- `decode` interprets code as a boundary constraint.
- `Guard` is a single *admissible step* of the system.
- `Flow` (from `GTruth`) is the boundary‑level meaning of that step.

This is the hook that makes “logic eats itself” precise: meta‑reasoning is
phrased at `decode` level and transported via canonical folds.

### Minimal entry points (recommended imports)
- Minimal core: `LogOS/API/Minimal.agda`
- Kernel interface: `LogOS/Kernel.agda`
- Initial/canonical kernels: `LogOS/Kernel/Initial.agda` and `LogOS/Kernel/Infinite/Initial.agda`
- Curated packs: `LogOS/Packs/ZFC/All.agda`, `LogOS/Packs/Universality/All.agda`

Application Packs (What You Get)
--------------------------------
This repo is organized so “big theorems” are opt‑in packs that do *not* contaminate
the kernel.

### ZFC (as a kernel application)
- Narrative: `docs/Application_ZFC.lagda.md`
- Pack: `LogOS/Packs/ZFC/All.agda`
- Stable surface: `LogOS/Packs/ZFC/All.agda` (pack-first)

### Computational universality (Universality + UniversalIR)
- Narrative: `docs/Application_Universality.lagda.md`
- Stable surfaces: `LogOS/Models/Universality/Core.agda`, `LogOS/Models/UniversalIR/Core.agda`
- Pack bundle: `LogOS/Packs/Universality/All.agda` (re-exports both)

### Complexity (verification vs search; physical bottlenecks)
- Narrative: `docs/Complexity.lagda.md`
- Stable surface: `LogOS/Models/Complexity/Core.agda`
- Physical separation story: `docs/Application_PvsNP.lagda.md`
- P vs NP claim pack (correctness-carrying, packaging only): `LogOS/Domain/Complexity/PvsNP.agda`

### Opacity (observability ledgers; GRH as a conditional application)
- Narrative: `docs/Application_Opacity.lagda.md`
- Stable surface: `LogOS/Models/Opacity/Core.agda`
- GRH application surface: `LogOS/Models/Opacity/Applications/GRH.agda`
- Vacuity guards (non-vacuity / non-tautology): `LogOS/Domain/Opacity/Meaningfulness.agda`
- Guarded GRH pack surface: `LogOS/Domain/Opacity/GRH.agda`
  (re-exports `LogOS/Domain/Opacity/GRH_Vacuity_Guards.agda`).

Formal Attachments (Classic Logic + HoTT Reading)
-------------------------------------------------
Two companion documents make the “math paper” story explicit, and a third provides a non-canonical
physics-aligned reading:

- **Multi-institution (classic model theory):** `docs/View_MultiInstitution.lagda.md`
- **3-level HoTT positioning note:** `docs/View_HoTT_3Level.lagda.md`
- **Categorical logic view:** `docs/View_CategoricalLogic.lagda.md`
- **Observer semantics (physics-aligned view):** `docs/View_ObserverSemantics.lagda.md`

Both are documentation artefacts; the implementation truth is always the Agda
code under `LogOS/*` (including `LogOS/Domain/*`), plus the host surface wrappers in `Data/*`.

Where to Find the Exact Definitions
-----------------------------------
- Research-grade record/law listing: `docs/Definition_Spec.lagda.md`
- Curated CI surface: `make ci`
