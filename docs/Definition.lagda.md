<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% LogOS (Agda) — Start Here (Architecture, Kernel I/O, Packs)

```agda
{-# OPTIONS --safe #-}
module docs.Definition where

-- Sync guard: these imports are the public surfaces this document describes.
-- If they drift, the docs build fails.
open import LogOS.API.Minimal
import LogOS.API.Architecture as Architecture
open import LogOS.Packs.ZFC.Surface as ZFC
open import LogOS.Packs.Complexity.Surface as Complexity
open import LogOS.Packs.Universality.Surface as Universality
open import LogOS.Packs.UniversalIR.Surface as UniversalIR
open import LogOS.Packs.Opacity.Surface as Opacity
open import LogOS.Packs.Agents.Surface as Agents
```

This file is the recommended entry point for new users of the published LogOS
library. It explains the architecture, the Kernel “I/O surface”, and how the
major application packs (ZFC, complexity, universality/IR, opacity, plus the
Agents pack) hang together.

If you want the *research‑grade* “list of records and laws” definition, see:
`docs/Definition_Spec.lagda.md`.

Repository Map
--------------
At the top level:
- `LogOS/*` — the core logic and the Kernel interface (small, host‑minimal).
- `LogOS/Algebra/*` — small algebraic surfaces (e.g. braiding, graph surface).
- `LogOS/QAdapters/*` — ready‑made quantitative adapters (`QAdapter` instances).
- `LogOS/Domain/*` — application/domain developments (ZFC, Complexity, UniversalIR, …).
- `LogOS/Packs/*` — curated, publication-facing entrypoints (ZFC, Universality, UniversalIR, Opacity, Complexity, Agents, …).
- `docs/*` — narrative docs (this file + topic guides).
- `Tests/*` — regression aggregation for CI.

Hexagonal Architecture (Ports/Adapters)
---------------------------------------
The library uses a hexagonal (ports/adapters) structure:

- **Core (ports):** minimal interfaces and laws live under `LogOS/Minimal/*` and
  are combined as the `LogOS/Kernel` record.
- **Adapters:** canonical transports and translations live under:
  - `LogOS/Kernel/*` (reindexing, initiality, folds)
  - `LogOS/Ports/Semantic/*` (boundary presentations + canonical interlingua)
  - `LogOS/Adapters/Views/*` (signature/kernel/presentation/process adapters)
  - `LogOS/Theorems/*`, `LogOS/Algebra/*` (laws and derived structure)
- **Domain packs:** ZFC / complexity / physics live under `LogOS/Domain/*`
  and depend only on the ports + adapters.

This keeps “what the logic *is*” separate from “how we *use* it”.

An OO reading (without mutable state) is:
**OO reinterpreted through hexagonal architecture + category theory—objects as interface‑bearing semantic
points in a network, rather than stateful records with methods.**

- “Object” = a `Kernel`/`LogicKernel` instance (`LogOS/Kernel.agda`, `LogOS/Kernel/LogicKernel.agda`).
- “Interface/port” = boundary I/O + presentations (`LogOS/Boundary/IO.agda`, `LogOS/Boundary/Port.agda`).
- “Adapter” = canonical translation / view transport (`LogOS/Ports/Semantic/Interlingua.agda`, `LogOS/Kernel/Reindex.agda`).
- “Composition/wiring” = categorical process/kernels morphisms (`LogOS/Computation/SchemeCategory.agda`, `LogOS/Kernel/HomOverSig.agda`).

Canonical map of these layers:
- `LogOS/API/Architecture.agda`
- `docs/Architecture_PortsAdapters.lagda.md`

Host-Minimal Surface (Portability Claim)
----------------------------------------
To make “LogOS could be hosted elsewhere” precise, the repo enforces a tiny host
surface: only a short list of files may import `Agda.Builtin` modules / `Agda.Primitive`.
Everything else depends on these wrappers.

See `scripts/host_surface_check.sh` for the enforced allowlist:
- `Host/Level.agda`
- `Data/Nat.agda`
- `Data/Bool.agda`
- `Data/List.agda`
- `Data/Maybe.agda`
- `Data/Relation/Binary/PropositionalEquality.agda`

Kernel in One Page
------------------
Technically, the kernel is parameterized by:
- a signature `Sig : LogOSSignature ℓ` (cospan‑shaped world/boundary carriers + operations), and
- a quantitative adapter `Q : QAdapter ℓ`, where `Scale` is a finite‑join unital quantale
  (budgets/grades) and `Time` embeds into `Scale` via `τ`.
The optional graded kernel (`LogOS/Kernel/Graded.agda`) indexes the guarded flow as `Flow : Scale → Con_bnd → Con_bnd`.
In this file, `Con_bnd` means the **boundary constraint** carrier (the `Con` of the boundary preorder), i.e.
`ConPoset.Con (BulkBoundary.bnd BB)` in the Kernel record.

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
  With optional ω-limit structure (`OmegaCPO` + `FiniteFirst`) one can prove μ‑induction
  (leastness among `Flow`‑stable constraints, in the boundary preorder). With optional
  antisymmetry you can read that leastness at the level of equality.

The coherence you must provide is explicit:
- `coh-LH` links S‑truth to H‑truth via a translation `TransH : Fml → Con_bnd`.
- `sat-coh` links world‑indexed H‑truth to boundary‑indexed H‑truth via `to∂`.

```agda
-- Anchor: signature-level boundary wiring (avoid confusion with the constraint-level
-- `ext/bnd` adjunction in `Kernel.Holo`).
to∂-anchor
  : ∀ {ℓ} (Sig : LogOSSignature ℓ)
  → LogOSSignature.Cosp Sig → LogOSSignature.∂Cosp Sig
to∂-anchor Sig = LogOSSignature.to∂ Sig

from∂-anchor
  : ∀ {ℓ} (Sig : LogOSSignature ℓ)
  → LogOSSignature.∂Cosp Sig → LogOSSignature.Cosp Sig
from∂-anchor Sig = LogOSSignature.from∂ Sig
```

### Kernel I/O surface (the reflective boundary)
Every Kernel exposes a tiny “I/O” API that makes inference steps speak about
themselves *inside* the logic:

- `encode : Con_bnd → Code`
- `decode : Code → Con_bnd` with `decode (encode c) ≡ c` (pointwise; no function extensionality assumed)
- `Guard : Code → Code` (one guarded step on code)
- `GTruth` exposes `Flow : Con_bnd → Con_bnd` (closure step on constraints)
- the fundamental coherence law (unguarded kernel):
  - `decode (Guard γ) ≡ Flow (decode γ)`
  - graded variant: `decode (Guard γ) ≡ Flow step-grade (decode γ)` and the distinguished fixed point is
    characterized at `Flow sat` (see `docs/Definition_Spec.lagda.md`).

Intuition:
- `Code` is the internal language of “programs / proofs / processes”.
- `decode` interprets code as a boundary constraint.
- `Guard` is a single *admissible step* of the system.
- `Flow` (from `GTruth`) is the boundary‑level meaning of that step.

This is the hook that makes “logic eats itself” precise: meta‑reasoning is
phrased at `decode` level and transported via canonical folds.

### Minimal entry points (recommended imports)
- Minimal core: `LogOS/API/Minimal.agda`
- Unified kernel interface: `LogOS/API/LogicKernel.agda` and `LogOS/Kernel/LogicKernel.agda`
- Concrete kernel interface (unguarded G-tier): `LogOS/Kernel.agda`
- Initial/canonical kernels: `LogOS/Kernel/Initial.agda` and `LogOS/Kernel/Infinite/Initial.agda`
- Curated packs: `LogOS/Packs/ZFC/All.agda`, `LogOS/Packs/Universality/All.agda`, `LogOS/Packs/Agents/All.agda`

One System, Four Views (Unifier)
-------------------------------
The codebase is organised so the same core interface admits multiple, mutually consistent
readings without changing the kernel:

- View notes:
  - Multi-institution: `docs/View_MultiInstitution.lagda.md`
  - 3+ level HoTT-style: `docs/View_HoTT_3Level.lagda.md`
  - 2-category logic: `docs/View_CategoricalLogic.lagda.md`
  - Observer semantics: `docs/View_ObserverSemantics.lagda.md`

- **Multi-institution:** S/H/G tiers as linked institutions; reindexing along signature maps is implemented
  by `LogOS/Kernel/Reindex.agda` (and packaged heterogeneously in `LogOS/Kernel/HomOverSig.agda`).
- **3+ level HoTT-style:** S/H/G are explicit tiers of truth glued by equivalences/coherences; the reflection/code
  layer provides the “+” (`encode/decode/Guard` in `LogOS/Kernel/Core.agda` / `LogOS/Kernel.agda`).
- **2-category theory:** kernels (and their instances) form a preorder-enriched 2-dimensional refinement calculus
  (`LogOS/Kernel/LogicKernel/Hom2Cat.agda`; wrapper records in `LogOS/Theorems/CategoryTheory/WrapperCore.agda`,
  instantiated in `LogOS/Theorems/CategoryTheory/Kernel2Cat.agda`).
- **Observer semantics:** “observer steps” are monotone endomaps on boundary constraints ordered by refinement
  (`LogOS/Kernel/EndoCore.agda`, `LogOS/Kernel/TensorDSL.agda`).

Application Packs (What You Get)
--------------------------------
This repo is organized so “big theorems” are opt‑in packs that do *not* contaminate
the kernel.

### ZFC (as a kernel application)
- Narrative: `docs/Application_ZFC.lagda.md`
- Pack: `LogOS/Packs/ZFC/All.agda`
- Stable surface: `LogOS/Packs/ZFC/All.agda` (pack-first)
- Forcing-like closure surface: `LogOS/Domain/ZFC/SetTheory/Dsl.agda`,
  `LogOS/Domain/ZFC/SetTheory/StageToCHFromHierarchy.agda` (`μFlow` when `OmegaCPO` + `FiniteFirst` are supplied)

### Computational universality (UniversalIR)
- Narrative: `docs/Application_Universality.lagda.md`
- Stable surfaces: `LogOS/Packs/UniversalIR/Core.agda`, `LogOS/Packs/UniversalIR/Agreement.agda`
- Pack bundle: `LogOS/Packs/Universality/All.agda` (UniversalIR-first bundle)
- Meta-language refinement (scheme/process + contracts): `LogOS/MetaLanguage/All.agda`

### Complexity (verification vs search; physical bottlenecks)
- Narrative: `docs/DeepDive/Complexity.lagda.md`
- Stable surfaces: `LogOS/Packs/Complexity/Core.agda`, `LogOS/Packs/Complexity/PhysicsOfInformation.agda`
- Physical separation story: `docs/Application_Complexity.lagda.md`

### Opacity (observability ledgers; conditional application)
- Narrative: `docs/Application_Opacity.lagda.md`
- Stable surface: `LogOS/Packs/Opacity/Core.agda`
- Optional application surfaces: `LogOS/Packs/Opacity/Applications/*`
- Vacuity guards (non-vacuity / non-tautology): `LogOS/Domain/Opacity/Meaningfulness.agda`
  - Note: spectral claims (including GRH-style) live here as *conditional applications* (kept out of the core narrative).

### Agents (sockets + monitoring/auditing)
- Narrative: `docs/Application_Agents.lagda.md`
- Pack bundle: `LogOS/Packs/Agents/All.agda`
- Meta-language surface: `LogOS/Packs/Agents/MetaLanguage.agda`
- Kernel-as-process constructors: `LogOS/Packs/Agents/Socket/FromKernel.agda`, `LogOS/Packs/Agents/Socket/FromGradedKernel.agda`
- Heterogeneous networks: `LogOS/Packs/Agents/Networks/Hetero.agda`
- Network-as-agent wrapper: `LogOS/Packs/Agents/Networks/NetworkAgent.agda`
- Opacity hook (budgeted “no total auditor”): `LogOS/Packs/Agents/Safety/NoTotalAuditor.agda`

Formal Attachments (Classic Logic + HoTT Reading)
-------------------------------------------------
Companion documents make the “math paper” story explicit (as alternative readings of the same kernel):

- **Multi-institution (classic model theory):** `docs/View_MultiInstitution.lagda.md`
- **3-level HoTT positioning note:** `docs/View_HoTT_3Level.lagda.md`
- **Categorical logic view:** `docs/View_CategoricalLogic.lagda.md`
- **Observer semantics (physics-aligned view):** `docs/View_ObserverSemantics.lagda.md`

These are documentation artefacts; the authoritative source of truth is the Agda
code under `LogOS/*` (including `LogOS/Domain/*`), plus the host surface wrappers in `Data/*`.

Meta-theory sanity checks
-------------------------
The repo includes a small set of typechecked “view coherence” checks that exercise the bridge points
between these presentations without adding axioms:

- `Tests/ViewsMetaTheory.agda`

Where to Find the Exact Definitions
-----------------------------------
- Research-grade record/law listing: `docs/Definition_Spec.lagda.md`
- Curated CI surface: `make ci`
