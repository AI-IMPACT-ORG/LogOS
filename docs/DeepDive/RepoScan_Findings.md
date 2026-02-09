<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Repo Scan Findings — Design Philosophy Alignment (2026-02-06)

This is a repo-wide “architecture smell” scan focused on the README design philosophy:
layering discipline, explicit ports/adapters boundaries, prototypeity, and stable vs experimental trust surfaces.

The goal is practical: get real functionality wins by making the codebase easier to extend safely (by humans + agents),
and by shrinking the diff surface of changes (smaller blast radius).

Interpretation (analogy): This document uses software-engineering vocabulary (“architecture smells”, “blast radius”)
as an analogy for dependency-coupling risk, not as a literal theorem statement.

## Highest-leverage standardisation wins (shortlist)

1. **Eliminate cross-layer imports** (shrink `scripts/layer_order_allowlist.txt` to zero).
2. **Make “Surface vs All vs Core” consistent**:
   - Topic libraries: `All` = index/discoverability, `Surface` = umbrella navigation surface.
   - Packs: `Core` = minimal curated surface; `All` = batteries-included umbrella; `Surface` = stable import surface.
3. **Stop importing internal kernel modules from topic libraries**; prefer `LogOS.API.Kernel` (or a minimal interface),
   to reduce coupling and keep internal kernel refactors cheap.
4. **De-duplicate pack trust metadata** so `packTrust` cannot drift between `Core` / `All` / `Surface`.
5. **Move bridge modules upward**: kernel→boundary glue should live in boundary/theorems (not under `LogOS/Kernel/*`).

## Layering violations (current allowlist)

These are concrete “wrong direction” imports against the README architecture diagram.
They are currently allowlisted as a migration scaffold in `scripts/layer_order_allowlist.txt`.

### Algebra layer importing Minimal/Kernel (should be re-homed or split)

- Fixed: `LogOS/Theorems/Boundary/Kernel/Braiding.agda` (moved out of Algebra; kernel-dependent theorem/module).
- Fixed: `LogOS/Minimal/ConAlg.agda` (constraint-algebra interface lives in Minimal).
- Fixed: `LogOS/Minimal/Prequantale.agda` (prequantale interface lives in Minimal; legacy `Quantale` compatibility alias removed).

### Free layer importing Minimal (foundations ↔ minimal interface split is blurry)

- Fixed: free-constraint algebra modules live in Minimal:
  `LogOS/Minimal/Constraints.agda`, `LogOS/Minimal/ConstraintsIndexed.agda`, `LogOS/Minimal/ConstraintsOverSig.agda`.

### Host/Prelude importing Syntax (prototypeity boundary is inverted)

- Fixed: `LogOS/Host/Empty.agda` defines `⊥` / `⊥-elim` at the Host layer (no upward imports).
- Fixed: `LogOS/Prelude.agda` defines `¬_` and `LogOS/Prelude/*` no longer import `LogOS.Syntax.Prop` for basic negation/emptiness.

### Syntax importing Kernel/Minimal (should move to Kernel or become parametric)

- Fixed: decoded-equality aliases live at `LogOS/Kernel/Eq.agda` (module `LogOS.Kernel.Eq`).

### Kernel importing Boundary/System (bridge modules live in the wrong layer)

- Previously: kernel-layer bridge modules imported Boundary/System.
  These have been moved upward to the boundary layer:
  - `LogOS/Boundary/FromKernel.agda`
  - `LogOS/Boundary/FromGradedKernel.agda`
  - `LogOS/Boundary/KernelVacuityGuards.agda`

### Computation importing Boundary/Ports/Theorems (compute layer mixing)

- Fixed: `LogOS/Computation/SchemeCategory.agda` no longer imports `LogOS.Boundary.Telemetry` / `LogOS.Ports.Semantic.*`;
  SatSystem bridge moved to `LogOS/Ports/Semantic/SchemeCategorySatSystem.agda`.
- Fixed: `LogOS/Computation/ProcessLimit.agda` uses μ-fusion core from `LogOS/Minimal/MuFusion.agda`.

### Ports importing Theorems (ports should not depend on proof packages)

- Fixed: `LogOS/Ports/Semantic/InterlinguaMu.agda` now imports μ-fusion core from `LogOS/Minimal/MuFusion.agda`.
- Fixed: `LogOS/Ports/Semantic/InterlinguaCodeKernel.agda` no longer imports `LogOS.Theorems.Boundary.OmegaCPOMapKit`.

## Topic libraries importing internal kernel modules (API boundary bypass)

Previously, many topic modules directly `open import LogOS.Kernel*` (bypassing the intended API boundary).
This has now been standardised:

- Fixed: topic libraries import kernel pieces via `LogOS.API.Kernel*` wrappers (not `LogOS.Kernel*`).
- Guardrail: `scripts/topic_kernel_api_check.sh` enforces this for `LogOS/{ZFC,Universality,UniversalIR,Complexity,ObjectLogic,InfoTheory}`.

**Why this matters:** internal kernel refactors become expensive because topic libraries depend on internal structure.

**Fixed:** topic libraries now depend on `LogOS.API.Kernel*` (and wrapper modules under `LogOS.API.Kernel.*`),
keeping internal kernel modules behind a stable API surface.

## Pack trust (`packTrust`) duplication/drift risk

Previously, multiple packs defined `packTrust` in more than one module (typically both `Core` and `All`),
which is a latent drift hazard.

- Fixed: pack `All` modules delegate `packTrust` to their corresponding `Core` (single source of truth).
- Fixed: `LogOS/Packs/Complexity/Experimental/PhysicsOfInformation.agda` delegates `packTrust` to `LogOS.Packs.Complexity.Experimental.Core.packTrust`.

**Fixed:** `packTrust` is single-sourced per pack (at `Core`) and re-exported by higher pack surfaces.

## Surface discipline / index discipline (All vs Surface vs Core)

The repo is moving toward a clean pattern, but it is not fully consistent yet:

- Topic libraries are trending toward `All` as index and `Surface` as umbrella navigation surface (good).
- Some non-topic namespaces still use `All` as a public umbrella and others use `Surface`.
- Several “All” modules in packs/theorems/ports are deliberately umbrella-style; that’s fine, but the pattern should be documented and uniform.

**Fixed:** convention is documented in `docs/DeepDive/API_Surfaces.lagda.md` and enforced by
`scripts/topic_all_index_check.sh` (wired into `make ci-policy`).

## Bridge placement (ports/adapters vs theorems)

Some modules sit at a boundary where they look like theorems but live under “operational” namespaces (Computation/Ports).
This increases coupling:

- Fixed: μ-fusion transport core lives in `LogOS/Minimal/MuFusion.agda` (reused by Ports/Computation without importing Theorems).
- Fixed: ports no longer import ωCPO-map theorem kits (semantic transport uses lower-layer interfaces).

**Fixed (policy):** choose (B): lower reusable lemma cores into a lower layer so Ports/Computation can reuse them
without importing Theorems. Guardrail: `scripts/operational_no_theorems_imports_check.sh` (wired into `make ci-policy`).

## Boundary telemetry leaking into computation

Previously `LogOS/Computation/SchemeCategory.agda` depended on telemetry + semantic port types.
This has been standardised:

**Fixed:** `LogOS/Computation/SchemeCategory.agda` is telemetry/port-agnostic; the SatSystem bridge lives in
`LogOS/Ports/Semantic/SchemeCategorySatSystem.agda`.

## Domain containment (stability boundary)

The README says stable roots must not reach `LogOS/Domain/*` transitively; checks enforce this.

**Fixed:** domain navigation surfaces exist (`LogOS.Domain.All` index + `LogOS.Domain.Surface` umbrella) while stable pack
surfaces remain protected by `scripts/stable_surface_no_domain_imports_check.sh`.

## Hygiene / repo maintenance (small but constant wins)

- Fixed: build/tool artifacts stay out of the repo (`.github/cabal-index-state.txt` is ignored via `.gitignore`).
- Keep `.DS_Store` out of tracked paths (Mac metadata).
- Prefer anchored navigation roots for new modules so reachability doesn’t regress (CI reachability check is working; keep using it).
