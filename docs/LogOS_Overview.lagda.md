<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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
- `LogOS/{ZFC,UniversalIR,Universality,Complexity,InfoTheory}/*` — mature topic libraries (domain developments safe to depend on from stable packs).
- `LogOS/Domain/*` — quarantined experimental domains (currently: Opacity).
- `LogOS/ObjectLogic/*` — object logics (FOL/ND, ZF/ZFC sentences) used by some packs/views.
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
- **Domain developments:** most large developments live as topic libraries under
  `LogOS/{ZFC,UniversalIR,Universality,Complexity,InfoTheory}/*` and stay within the safe core
  (no direct `Agda.*` host imports; prefer the allowlisted `LogOS/Host/*` wrappers via `LogOS.Prelude`).
  Truly experimental domains are quarantined under `LogOS/Domain/*` (Opacity), and stable pack surfaces are CI‑enforced to not reach that namespace transitively.

This keeps “what the logic *is*” separate from “how we *use* it”.

Wording discipline (guardrail)
------------------------------
Canonical vocabulary and claim kinds live in:

- Terminology (literature ↔ LogOS): `docs/Terminology.lagda.md`.
- Claim/assumption discipline (literal vs conditional, vacuity guards, typed anchors):
  `docs/Kernel/ClaimRegister.lagda.md`.

When precision matters in prose, always name the relation: propositional
equality (`≡`), refinement (`⊑`), mutual refinement (`≈`), satisfaction
equivalence (`↔`), observational equality (`ObsEq…`), or adapter equivalence
(`Adapter≈`).

In particular, “truth” in LogOS is tiered and local:
- **Strict truth (S-tier):** satisfaction of strict formulas (`Sat_S` in the codebase).
- **Boundary truth (H-tier):** world‑indexed satisfaction of boundary constraints (`Sat_H`), coherent with boundary‑indexed `Sat_H_bnd` via `sat-coh`.
- **Stable truth (G-tier):** the distinguished lax fixed-point witness `Th*` for the guarded flow `Flow` (interpretation: “global stable truth”).
  Leastness/μ‑induction is only available under extra domain structure (ω‑sups + continuity).

Interpretation labels (analogy)
-------------------------------
Interpretive labels (“kernel”, “channel”, “RG”, “GRH”, …) are used for
orientation only; the formal content is the cited Agda surface.

For the canonical communication/boundary framing (including an OO‑shaped reading
of ports/adapters), see `docs/DeepDive/Communication.lagda.md`.

For the ports/adapters spine, see `docs/DeepDive/Architecture_PortsAdapters.lagda.md`
and the curated map `LogOS/API/Architecture.agda`.

Host-Minimal Surface (Portability Claim)
----------------------------------------
To make “LogOS could be hosted elsewhere” precise, the repo enforces a tiny host
surface: only a small allowlisted subset of `LogOS/Host/**` may import
`Agda.Builtin.*` / `Agda.Primitive` (see `scripts/host_surface_check.sh`).

Everything else should import `LogOS.Prelude` (which re-exports the wrappers),
not `Agda.*` directly.

Enforced checks:
- allowlist: `scripts/host_surface_check.sh`
- no direct `LogOS.Host.*` imports outside the bridge: `scripts/host_import_check.sh`

Kernel in One Page
------------------
The kernel is parameterized by:

- a signature `Sig : LogOSSignature ℓ` (world/boundary carriers + operations), and
- a quantitative adapter `Q : QAdapter ℓ` (a prequantale‑like budget/grade algebra; finite joins by default).

In this file, `Con_bnd` means the carrier of boundary constraints: the `Con` of
the boundary preorder.

Integrated kernel interfaces:

- `KernelShape` (`LogOS/Kernel/Shape.agda`): S/H/G tiers, boundary I/O, and reflection.
- `Kernel` (`LogOS/Kernel.agda`) and `GradedKernel` (`LogOS/Kernel/Graded.agda`): concrete integrated records.
- `Kernel` (`LogOS/Kernel.agda`): the canonical surface that integrates S/H/G truth with reflection.
  ungraded and graded kernels share the same API.
- Boundary-first packaging (“open systems”): `System` (`LogOS/System.agda`) bundles a `BoundaryIO` with its ambient signature/world/truth data and exposes the induced boundary satisfaction system and canonical boundary port.

Truth is tiered and local:

- S-tier: strict formulas + `Sat_S`.
- H-tier: world‑indexed `Sat_H w c` and boundary‑indexed `Sat_H_bnd (to∂ w) c`, related by `sat-coh`.
- G-tier: guarded closure `Flow` and distinguished witness `Th*` (a lax fixed point by default).

Limit strength is assumption‑scoped: Kleene `μ` / μ‑induction, and derived transport theorems
(`Th*≈μFlow`, μ‑fusion) require explicit ω‑sup/continuity hypotheses (see
`docs/Kernel/ClaimRegister.lagda.md`).

Reflection makes computation speak: `Code`, `decode`, `encode`, and one-step
`FlowCode = Guard ∘ Body` with decode commutation laws (see
`docs/DeepDive/Communication.lagda.md`).

Full record/law details: `docs/LogOS_Core_Spec.lagda.md`.

Bootstrapping (theorem surface)
-------------------------------
Bootstrapping is the forced interlingua translation between two canonical ports
induced by a kernel (code port ↔ boundary port). It is packaged as adapter
equivalence (`Adapter≈`) and uniqueness up to `Adapter≈`, not as an ad‑hoc
compiler.

See `docs/DeepDive/Architecture_PortsAdapters.lagda.md` and
`LogOS/Theorems/Meta/Bootstrapping.agda`.

Pass calculus (transpiler view)
-------------------------------
Adapters compose into pipelines; the generic pass calculus is:

- `LogOS/Theorems/Meta/Transpiler.agda` (`Transpiler`, `Pipeline`, `Iso`)
- `LogOS/Theorems/Meta/CHL/Interoperability.agda` (CHL-facing `compile` passes)
- `LogOS/Theorems/Meta/Transpiler/Operational.agda` (small-step/n-step skeleton + decode simulation)

All correctness statements are phrased up to satisfaction equivalence (↔) / adapter
equivalence (`Adapter≈`) rather than by syntactic identification.

Safety spine (design choice → architecture)
-------------------------------------------
The kernel makes a deliberate design choice: it supplies only the core
interface (no built-in provability/comprehension). Paradox-enabling structure is
kept explicit and optional.

See `docs/Meta_Safety.lagda.md` and `LogOS/Theorems/Meta/Safety/All.agda`.

CHL capstone (brutally honest)
------------------------------
LogOS includes a kernel-native Curry–Howard–Lambek (CHL) view that stays
preorder-safe and proof-relevant (no hidden antisymmetry/proof-irrelevance).

- View note: `docs/Views/CurryHowardLambek.lagda.md`
- Ultra-compact kernel core (Meredith-style anchors): `docs/Views/MeredithSentences.lagda.md`
- Formal surfaces: `LogOS/Theorems/Meta/CHL/*` (including assumption-scoped completeness)

Minimal entry points (recommended imports)
-----------------------------------------
- Minimal core: `LogOS/API/Minimal.agda`
- Unified kernel interface: `LogOS/API/Kernel.agda` and `LogOS/Kernel.agda`
- Canonical bridge connectors: `LogOS/API/Bridges.agda`
- Concrete kernel interface (ungraded G-tier): `LogOS/Kernel/UngradedKernel.agda`
- Initial/canonical kernels: `LogOS/Kernel/UngradedKernel/Initial.agda` and `LogOS/Kernel/UngradedKernel/Infinite/Initial.agda`
- Stable lock surfaces: `LogOS/Packs/ZFC/Surface.agda`, `LogOS/Packs/Universality/Surface.agda`, `LogOS/Packs/Agents/Surface.agda`

One System, Many Views (Unifier)
--------------------------------
The same kernel interfaces admit multiple expert-facing readings without
changing the kernel. The views are documentation artefacts (typechecked sync
guards); they do not add axioms.

Start at `docs/Views/All.lagda.md` and pick a view note (each includes a small
dictionary + a residual-vs-literature paragraph).

Navigation
----------
- Pack navigation landing page: `docs/Library.lagda.md`
- Applications: `docs/Applications/`
- Views (one kernel, many readings): `docs/Views/All.lagda.md`
- Deep dives (implementation and motivation): `docs/DeepDive/`
- Meta safety spine: `docs/Meta_Safety.lagda.md`

Checks
------
- Policy/lint: `make ci-policy`
- Warm strict development loop: `make check-quick` (or `make check-quick-no-transformer` outside transformer work)
- Cold full publication/CI gate: `make check-all`
- Docs typecheck: `bash scripts/check_all_docs.sh`
- View/meta-theory regression: `Tests/ViewsMetaTheory.agda`
