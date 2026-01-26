<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% LogOS (Agda) — Start Here (Architecture, Kernel I/O, Packs)

```agda
{-# OPTIONS --safe #-}
module docs.LogOS_Overview where

open import LogOS.API.Architecture as Architecture
open Architecture.Downstream
```

This file is the recommended entry point for new users of the published LogOS
library. It explains the architecture, the Kernel “I/O surface”, and how the
major application packs (ZFC, complexity, universality/IR, opacity, plus the
Agents pack) hang together.

If you want the *research‑grade* “list of records and laws” definition, see:
`docs/LogOS_Core_Spec.lagda.md`.

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
- **Domain packs:** ZFC / complexity / physics-of-information developments live under `LogOS/Domain/*`
  and stay within the safe core (no direct `Agda.*` host imports; prefer the allowlisted `LogOS/Host/*` wrappers via `LogOS.Prelude`).

This keeps “what the logic *is*” separate from “how we *use* it”.

Wording discipline (guardrail)
------------------------------
The docs try to distinguish four kinds of statements:

- **Literal (checked):** an Agda definition/lemma in the referenced file.
- **Truth after computation (stabilized):** a statement about a closure/fixed
  point (e.g. `Th*`, `Box`, `μ Flow`); by default this is only a *lax* fixed
  point unless ω‑sup/continuity assumptions are supplied.
- **Representational truth (presentation):** a statement transported through
  `decode`/`encode`/`translate`/`SatMor`, i.e. preserved up to the relevant
  satisfaction equivalence; this is not definitional equality.
- **Analogy / interpretation:** explanatory metaphors (kernel, channel, RG,
  “GRH”, …). These are explicitly marked as interpretations and never add
  logical power; the formal content is always the cited Agda surface.

In particular, “truth” in LogOS is tiered and local:
- **Strict truth (S-tier):** satisfaction of strict formulas (`SatS` in the codebase).
- **Boundary truth (H-tier):** satisfaction of boundary constraints (`Sat_H`), intended as communicable meaning.
- **Stable truth (G-tier):** the distinguished fixed-point witness `Th*` for the guarded flow `Flow`.
  Leastness/μ‑induction is only available under extra domain structure (ω‑sups + continuity).

Interpretation (analogy): an OO reading (without mutable state)
--------------------------------------------------------------
This is explanatory only (not a formal claim): you can read the architecture in
“OO words” as long as you keep the formal boundaries explicit.

- “Object” = a `Kernel`/`LogicKernel` instance (`LogOS/Kernel.agda`, `LogOS/Kernel/LogicKernel.agda`).
- “Interface/port” = boundary I/O + presentations (`LogOS/Boundary/IO.agda`, `LogOS/Boundary/Port.agda`).
- “Adapter” = canonical translation / view transport (`LogOS/Ports/Semantic/Interlingua.agda`, `LogOS/Kernel/Reindex.agda`).
- “Composition/wiring” = categorical process/kernels morphisms (`LogOS/Computation/SchemeCategory.agda`, `LogOS/Kernel/HomOverSig.agda`).

Canonical map of these layers:
- `LogOS/API/Architecture.agda`
- `docs/DeepDive/Architecture_PortsAdapters.lagda.md`

Host-Minimal Surface (Portability Claim)
----------------------------------------
To make “LogOS could be hosted elsewhere” precise, the repo enforces a tiny host
surface: only a short list of files may import `Agda.Builtin` modules / `Agda.Primitive`.
Everything else depends on these wrappers.

See `scripts/host_surface_check.sh` for the authoritative allowlist (mirrored here for convenience):
- `LogOS/Host/Level.agda`
- `LogOS/Host/Nat.agda`
- `LogOS/Host/Bool.agda`
- `LogOS/Host/List.agda`
- `LogOS/Host/Maybe.agda`
- `LogOS/Host/String.agda`
- `LogOS/Host/Relation/Binary/PropositionalEquality.agda`

Kernel in One Page
------------------
Technically, the kernel is parameterized by:
- a signature `Sig : LogOSSignature ℓ` (cospan‑shaped world/boundary carriers + operations), and
- a quantitative adapter `Q : QAdapter ℓ`, where `Scale` is a finite‑join unital quantale‑like
  structure (budgets/grades; no infinite‑join completeness is assumed here) and `Time` maps
  into `Scale` via the monoid homomorphism `τ`.
The optional graded kernel (`LogOS/Kernel/Graded.agda`) indexes the guarded flow as `Flow : Scale → Con_bnd → Con_bnd`.
In this file, `Con_bnd` means the **boundary constraint** carrier (the `Con` of the boundary preorder), i.e.
`ConPreorder.Con (BulkBoundary.bnd BB)` in the Kernel record.

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
  antisymmetry you can read that leastness at the level of equality. In that setting,
  `Th*` is equivalent (up to mutual refinement) to the Kleene fixed point `μ Flow`
  (`LogOS/Theorems/Boundary/ContinuityCore.agda`), and its preservation along maps can
  be derived from `Flow` commutation + ωCPO structure (`LogOS/Theorems/Boundary/MuFusion.agda`).
  These hypotheses are packaged explicitly as:
  - `ContinuityCore.For.MuData` (ωCPO + finite-first approximants), and
  - `MuFusion.For.Th*TransportAssumptions` (adds ω-continuity of `map` and the lax commutation law).

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
- **stable closure on code** (derived, but exposed as API for convenience):
  - ungraded: `Box : Code → Code` defined as `encode (Flow (decode γ))` (`LogOS/Kernel.agda`)
  - graded: `BoxAt g : Code → Code` and `Box = BoxAt sat` (`LogOS/Kernel/Graded.agda`)
  - uniform CHL-facing interface: `BoxAt`/`Box` for any `LogicKernel` (`LogOS/Kernel/LogicKernel.agda`)
  - port view: `Box` is `BoundaryPort.Extend CodePort Flow` for the canonical `CodePort`
    (`Box≡ExtendFlow` in `LogOS/Ports/Semantic/CanonicalPorts.agda`)
- the fundamental coherence law (unguarded kernel):
  - `decode (Guard γ) ≡ Flow (decode γ)`
  - graded variant: `decode (Guard γ) ≡ Flow step-grade (decode γ)` and the distinguished fixed point is
    characterized at `Flow sat` (see `docs/LogOS_Core_Spec.lagda.md`).

Intuition:
- `Code` is the internal language of “programs / proofs / processes”.
- `decode` interprets code as a boundary constraint.
- `Guard` is a single *admissible step* of the system.
- `Flow` (from `GTruth`) is the boundary‑level meaning of that step.

This is the hook that makes “logic eats itself” precise: meta‑reasoning is
phrased at `decode` level and transported via canonical folds.

Bootstrapping (theorem surface)
-------------------------------
Bootstrapping here is a direct consequence of the port calculus, not a bespoke
encoding trick.

Pass calculus (transpiler view)
-------------------------------
The same interlingua that forces bootstrapping yields a general transpiler
calculus. Any port adapter is a semantics-preserving pass, uniquely determined
by boundary satisfaction.

- `LogOS/Theorems/Meta/Transpiler.agda` provides `Transpiler`, `Pipeline`, and
  `Transpiler.Iso`.
- `LogOS/Theorems/Meta/Transpiler/Operational.agda` provides a minimal small-step
  and n-step operational semantics for kernel code (`FlowCode`) with a decode
  simulation lemma.
- `Transpiler.TypeSoundness` recasts pass correctness as preservation/reflection
  of judgments at any chosen observer.
- `Transpiler.Telemetry` lifts the same pass calculus to budgeted traces,
  including a generic budget‑weakening lemma.
- Bootstrapping is the canonical `Transpiler` instance for `Stage1Port → Stage0Port`.
- CHL transpilers (named `compile` in code) are exposed as transpiler instances
  (`Strict.Transpiler` and `Code.Transpiler`) in
  `LogOS/Theorems/Meta/CHL/Interoperability.agda`.

There are two presentations of the same boundary satisfaction:
- `CodePort`: formulas are `Kernel.Code`; import is `decode`; export/`Interp` is `encode`.
- `BoundaryPort∂`: the canonical boundary port (formulas are boundary constraints).
  Both live in `LogOS/Ports/Semantic/CanonicalPorts.agda`.

By interlingua, the translation between these ports is **forced**. In
`LogOS/Theorems/Meta/Bootstrapping.agda`:
- `bootstrap` is the canonical adapter `CodePort → BoundaryPort∂` (definitionally, see `bootstrap≡canonical`).
- `unbootstrap` is the export back to code (`encode`) with the built‑in port
  equivalence `Sat∂≈F`.
- The round‑trip laws are `translate-comp` + `translate-id`, not ad‑hoc proofs.
- `bootstrap-iso` packages the result as a port equivalence up to `Adapter≈`.
- `stage1→stage0-unique` / `stage0→stage1-unique` show adapters between stages
  are unique up to observation.
- The file also names `Stage0Port` (boundary) and `Stage1Port` (code) explicitly.
- `Pipeline` witnesses pass composition as adapter composition.
- `AsTranspiler` is the specialization of the general transpiler theorem
  (`LogOS/Theorems/Meta/Transpiler.agda`) to the stage0/stage1 ports.
- `bootstrap≡canonical` and `bootstrap-transpiler≡canonical` show the
  bootstrapping pass is definitionally the canonical transpiler.
- `Transpiler.Hetero` lifts the same story to satisfaction morphisms; the CHL
  strict/code transpilers are exposed as `compile-transpiler` instances in
  `LogOS/Theorems/Meta/CHL/Interoperability.agda`.
- `Transpiler.Iso` is the general quasi-inverse notion; `BootstrapIso` is just
  its specialization to the stage0/stage1 ports.
- `Telemetry` adds `telemetry-erasure` (traces do not change semantics) and
  budget weakening for trace order.
- `Telemetry.BudgetedBootstrap` bundles `bootstrap` with a trace‑derived budget.
- `FromGradedKernel` reuses the same theorem once a graded kernel is collapsed to `sat`.

So bootstrapping is a *corollary* of the core architecture: it is the
canonical interlingua between two presentations of the same boundary meaning.

Safety spine (design choice → architecture)
-------------------------------------------
The kernel makes a deliberate design choice: it supplies **only** the core
interface (no internal truth, provability, or comprehension). This forces the
boundary/port/guarded‑flow architecture and keeps paradox‑enabling structure
explicit and optional.

Formal spine + matrix:
- `LogOS/Theorems/Meta/Safety/DesignChoice.agda`
- `LogOS/Theorems/Meta/Safety/ArchitectureFromSafety.agda`
- `LogOS/Theorems/Meta/Safety/AvoidanceList.agda`
- `LogOS/Theorems/Meta/Safety/Matrix.agda` (paper-facing `SafetyMatrix`)

CHL capstone (brutally honest)
------------------------------
LogOS includes a kernel-native Curry–Howard–Lambek (CHL) view, but it is
preorder-safe and proof-relevant: everything is stated up to refinement /
observational equivalence, not definitional equality.

Exact claims (with proof surfaces):
- **Propositions / types / programs / proofs** are defined internally:
  `Type = Code`, `Prop = Code`, `Program = Refines`, `Proof = Refines`.
  See `LogOS/Theorems/Meta/CHL/Definition.agda`.
- **Soundness**: refinement implies semantic entailment at the H- and boundary
  tiers (`LogOS/Theorems/Meta/CHL/ModelTheory.agda`).
- **Category view**: codes form a thin category and `FlowCode` is a monotone
  endofunctor (`LogOS/Theorems/Meta/CHL/Category.agda`).
- **Capstone bundle**: the views above are packaged as a single theorem
  (`LogOS/Theorems/Meta/CHL/Capstone.agda`).

Non-claims (explicitly **not** assumed):
- No antisymmetry or proof-irrelevance is assumed.
- No global completeness for strict syntax without an explicit adequacy axiom.
- `TransH` is not assumed surjective onto boundary constraints.

Completeness is **relative**:
- Boundary-level completeness is available under a local adequacy assumption
  on the image of `to∂` (`LogOS/Theorems/Meta/CHL/Completeness.agda`).
- Strict-syntax completeness is available under the same adequacy assumption
  (`LogOS/Theorems/Meta/CHL/SyntaxCompleteness.agda`).
- Budgeted completeness is available when adequacy is assumed only for a chosen
  budget predicate on observations (`LogOS/Theorems/Meta/CHL/Completeness.agda`,
  `LogOS/Theorems/Meta/CHL/SyntaxCompleteness.agda`).
- Kernel-aligned budget predicate from telemetry:
  `LogOS/Boundary/Budget.agda`.
- Flow: choose a telemetry trace budget `b`, set `B = budget-from-trace b`,
  then assume `BudgetedAdequacy B` to obtain the budgeted completeness lemmas.
- Formula completeness under budgets is exposed as `completeF-budget` in
  `LogOS/Theorems/Meta/CHL/Definition.agda`.

### Minimal entry points (recommended imports)
- Minimal core: `LogOS/API/Minimal.agda`
- Unified kernel interface: `LogOS/API/LogicKernel.agda` and `LogOS/Kernel/LogicKernel.agda`
- Concrete kernel interface (unguarded G-tier): `LogOS/Kernel.agda`
- Initial/canonical kernels: `LogOS/Kernel/Initial.agda` and `LogOS/Kernel/Infinite/Initial.agda`
- Stable lock surfaces: `LogOS/Packs/ZFC/Surface.agda`, `LogOS/Packs/Universality/Surface.agda`, `LogOS/Packs/Agents/Surface.agda`

One System, Many Views (Unifier)
--------------------------------
The codebase is organised so the same core interface admits multiple, mutually consistent
readings without changing the kernel:

- View notes (index): `docs/Views/All.lagda.md`

- **Multi-institution:** S/H/G tiers as linked institutions; reindexing along signature maps is implemented
  by `LogOS/Kernel/Reindex.agda` (world-only `reindexKernel`, plus `reindexKernelWithFml` for strict-formula translation),
  and packaged heterogeneously in `LogOS/Kernel/HomOverSig.agda`.
- **3-level HoTT-style:** S/H/G are explicit tiers of truth glued by equivalences/coherences; the reflection/code
  layer provides the “+” (`encode/decode/Guard` in `LogOS/Kernel/Core.agda` / `LogOS/Kernel.agda`).
- **Categorical logic (2-category view):** kernels (and their instances) form a preorder-enriched 2-dimensional refinement calculus
  (`LogOS/Kernel/LogicKernel/Hom2Cat.agda`; wrapper records in `LogOS/Theorems/CategoryTheory/WrapperCore.agda`,
  instantiated in `LogOS/Theorems/CategoryTheory/Kernel2Cat.agda`), and boundary ports/adapters package into a
  boundary-level 2-category (`LogOS/Theorems/CategoryTheory/Port2Cat.agda`).
- **Observer semantics:** “observer steps” are monotone endomaps on boundary constraints ordered by refinement
  (`LogOS/Kernel/EndoCore.agda`, `LogOS/Kernel/TensorDSL.agda`).

Application Packs (What You Get)
--------------------------------
This repo is organized so “big theorems” are opt‑in packs that do *not* contaminate
the kernel.

### ZFC (as a kernel application)
- Narrative: `docs/Applications/ZFC.lagda.md`
- Pack: `LogOS/Packs/ZFC/All.agda`
- Stable lock surface: `LogOS/Packs/ZFC/Surface.agda` (umbrella: `LogOS/Packs/ZFC/All.agda`)
- Forcing-like closure surface: `LogOS/Domain/ZFC/SetTheory/Dsl.agda`,
  `LogOS/Domain/ZFC/SetTheory/StageToCHFromHierarchy.agda` (`μFlow` when `OmegaCPO` + `FiniteFirst` are supplied)

### Computational universality (UniversalIR)
- Narrative: `docs/Applications/Universality.lagda.md`
- Stable surfaces: `LogOS/Packs/UniversalIR/Core.agda`, `LogOS/Packs/UniversalIR/Agreement.agda`
- Stable lock surface: `LogOS/Packs/Universality/Surface.agda` (umbrella: `LogOS/Packs/Universality/All.agda`)
- Meta-language refinement (scheme/process + contracts): `LogOS/MetaLanguage/All.agda`

### Complexity (verification vs search; physical bottlenecks)
- Narrative: `docs/DeepDive/Complexity.lagda.md`
- Experimental surfaces: `LogOS/Packs/Complexity/Experimental/Core.agda`, `LogOS/Packs/Complexity/Experimental/PhysicsOfInformation.agda`
- Physical separation story: `docs/Applications/Complexity.lagda.md`

### Opacity (observability ledgers; conditional application)
- Narrative: `docs/Applications/Opacity.lagda.md`
- Experimental surface: `LogOS/Packs/Opacity/Experimental/Core.agda`
- Optional application surfaces: `LogOS/Packs/Opacity/Experimental/Applications/*`
- Vacuity guards (non-vacuity / non-tautology): `LogOS/Domain/Opacity/Meaningfulness.agda`
  - Note: spectral claims (including GRH-style) live here as *conditional applications* (kept out of the core narrative).
- Kernel-powered strengthenings (assumption weakenings): stable truth ⇒ observable (`TruthK→Pr`), meet-limit/cofinal scheduling, Hasse–Yoneda probe coverage
- One-line GRH wrappers (operator/nucleus/forcing/Weil): `LogOS/Domain/Opacity/Applications/GRH/Systems.agda`

### Information theory (Shannon-style interfaces)
- Narrative: `docs/Applications/InfoTheory.lagda.md`
- Stable lock surface: `LogOS/Packs/InfoTheory/Surface.agda` (umbrella: `LogOS/Packs/InfoTheory/All.agda`)
- Application wrappers: `LogOS/Packs/InfoTheory/Applications/All.agda`

### Agents (sockets + monitoring/auditing)
- Narrative: `docs/Applications/Agents.lagda.md`
- Stable lock surface: `LogOS/Packs/Agents/Surface.agda` (umbrella: `LogOS/Packs/Agents/All.agda`)
- Experimental extensions (transformer/scaling + physics/RG-flow/capstones): `LogOS/Packs/Agents/Experimental/Surface.agda` (umbrella: `LogOS/Packs/Agents/Experimental/All.agda`)
- Meta-language surface: `LogOS/Packs/Agents/MetaLanguage.agda`
- Kernel-as-process constructors: `LogOS/Packs/Agents/Socket/FromKernel.agda`, `LogOS/Packs/Agents/Socket/FromGradedKernel.agda`
- Heterogeneous networks: `LogOS/Packs/Agents/Networks/Hetero.agda`
- Network-as-agent wrapper: `LogOS/Packs/Agents/Networks/NetworkAgent.agda`
- Opacity hook (budgeted “no total auditor”): `LogOS/Packs/Agents/Safety/NoTotalAuditor.agda`
  - Proof-search instantiation (experimental): `LogOS/Packs/Agents/Experimental/Safety/NoTotalAuditor.agda`

Formal Attachments (Classic Logic + HoTT Reading)
-------------------------------------------------
Companion documents make the “math paper” story explicit (as alternative readings of the same kernel):

- Views index: `docs/Views/All.lagda.md`

These are documentation artefacts; the authoritative source of truth is the Agda
code under `LogOS/*` (including `LogOS/Domain/*`), plus the host surface wrappers in `LogOS/Host/*`.

Meta-theory sanity checks
-------------------------
The repo includes a small set of typechecked “view coherence” checks that exercise the bridge points
between these presentations without adding axioms:

- `Tests/ViewsMetaTheory.agda`

Where to Find the Exact Definitions
-----------------------------------
- Research-grade record/law listing: `docs/LogOS_Core_Spec.lagda.md`
- Curated CI surface: `make ci`
