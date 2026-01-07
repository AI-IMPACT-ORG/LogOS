<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# LogOS: an Agda research library for foundational logic system architecture.

LogOS is an Agda library for foundational logic architecture that treats the engineering of quite general logic systems as an application of modern software engineering methods.

The library is especially useful using code assistants like Claude Code, Codex, Cursor or similar. 

It features a small, host‑minimal kernel interface for a 3‑tier logic (S/H/G) with a reflective code surface, plus curated application packs (ZFC, complexity, universality/IR, opacity, agents). The same kernel supports multiple semantic views (multi‑institution, HoTT‑3‑level, categorical, observer semantics) without changing the core.

The main documentation lives in `/docs`. Uploading `docs/Definition_Spec.lagda.md` to a reasoning chatbot instantiates a conversational interface to start exploring the library. This uses the chatbot as an effective stochastic interpreter. Ensure memory features of the chatbot are switched off to avoid polluting cross-conversation chatbot memory. For bonus points: ask the chatbot to use the library to explain why this works based on density of information.


## Quickstart

Requirements: Agda `2.7.0.1`.

```sh
# Type-check the minimal API (no global libraries needed)
agda --no-libraries -i . LogOS/API/Minimal.agda

# Run policy checks + tests + docs
make ci
```

Optional publication sanity (heavier):

```sh
make check-all
```

Minimal “hello import”:

```agda
module Hello where
open import LogOS.API.Minimal
```

## Docs

Start here (literate Agda):
- Architecture + entrypoints: `docs/Definition.lagda.md`
- Research-grade spec: `docs/Definition_Spec.lagda.md`

Kernel views (polymorphicity): 
- Multi-Institution: `docs/View_MultiInstitution.lagda.md`
- Three level Homotopy Type Theory: `docs/View_HoTT_3Level.lagda.md`
- 2-Category view: `docs/View_CategoricalLogic.lagda.md` 
- Observer semantics: `docs/View_ObserverSemantics.lagda.md`

Applications:
- ZFC story: `docs/Application_ZFC.lagda.md`, `docs/DeepDive/ZFC_Demo.lagda.md`
- Complexity story: `docs/DeepDive/Complexity.lagda.md`, `docs/Application_Complexity.lagda.md`
- Universality story: `docs/Application_Universality.lagda.md`, `docs/Library.lagda.md`
- Opacity story: `docs/Application_Opacity.lagda.md`
- Agents story: `docs/Application_Agents.lagda.md`
- Conditional applications: see the relevant application notes under `docs/`

HTML docs (Agda HTML backend):
- Build locally: `make html` → `_build/html/index.html`

## Entry Points

Recommended import surfaces:
- Minimal API: `LogOS/API/Minimal.agda`
- Architecture map (ports/adapters spine): `LogOS/API/Architecture.agda`
- QAdapter instances: `LogOS/QAdapters/All.agda`
- Core theorem surface: `LogOS/Theorems/Core.agda`
- ZFC: `LogOS/Packs/ZFC/All.agda` (WFGraph quartets: `LogOS/Packs/ZFC/WFGraph.agda`)
- UniversalIR: `LogOS/Packs/UniversalIR/Core.agda` (bundle: `LogOS/Packs/Universality/All.agda`)
- Universality (toy core): `LogOS/Packs/Universality/Core.agda`
- Complexity: `LogOS/Packs/Complexity/Core.agda`
- Opacity: `LogOS/Packs/Opacity/Core.agda`
- Agents: `LogOS/Packs/Agents/All.agda` (meta-language: `LogOS/Packs/Agents/MetaLanguage.agda`)

## Trust Boundary

- The safe core is intended to be imported via `LogOS/API/Minimal.agda` and contains no global postulates.
- Models that need ω‑chain suprema supply them explicitly via `LogOS/Axioms/OmegaSup/Interface.agda` (`ChainSup`) and `omegaCPO-from-chainSup`.

Host surface (portability):
- Direct imports from `Agda.Primitive` / `Agda.Builtin.*` are intentionally restricted to a small allowlist:
  - `Host/Level.agda`
  - `Data/Nat.agda`
  - `Data/Bool.agda`
  - `Data/List.agda`
  - `Data/Maybe.agda`
  - `Data/Relation/Binary/PropositionalEquality.agda`
- CI enforces this via `make host-surface-check` (included in `make ci`).

## Build Targets

- `make ci` — policy checks + tests + docs
- `make packs` — type-check curated packs
- `make html` — build HTML docs into `_build/html/`
- `make check-all` — type-check every `*.agda` and `*.lagda.md` with `-W all -W error`

## License and Citation

- License: GPL-3.0-only (`LICENSE`)
- Citation metadata: `CITATION.cff`
- Changelog: `CHANGELOG.md`

<details>
<summary>Agda library setup (optional)</summary>

This library ships `LogOS.agda-lib`.

- Register in your global libraries file (e.g. `~/.agda/libraries`), then:
  - `agda -l LogOS LogOS/API/Minimal.agda`

Local setup note (library trouble):
- Quick fix: use `agda --no-libraries -i . LogOS/API/Minimal.agda` (no global config needed).
- If you prefer `-l LogOS` without touching `~/.agda/libraries`, create a repo-local
  `local.agda-libraries` file with the full path to `LogOS.agda-lib`, then run:
  `agda --library-file=local.agda-libraries -l LogOS LogOS/API/Minimal.agda`.

Using alongside agda-stdlib:
- This codebase ships minimal `Data.*` shims so it can build without stdlib.
- If you want to use agda-stdlib in the same project, prefer importing LogOS via the API modules and avoid mixing raw `Data.*` names.

</details>

<details>
<summary>Tensor / Endomap DSL (boundary-level “process calculus”)</summary>

This repo exposes a conservative DSL over monotone boundary endomaps:

- `LogOS/Kernel/TensorDSL.agda` (also re-exported by `LogOS/API/Minimal.agda`)
- Canonical fixed-point surface: `Th⋆K`, `FlowTh⋆K`, `Th⋆≤FlowTh⋆`, `FlowTh⋆≤Th⋆`
- Antisymmetry upgrade: `FlowTh⋆≡Th⋆` (alias: `fixedpoint-eq-under-antisym`)

</details>

<details>
<summary>Meta theorems quickstart (Rice/Tarski/Gödel/Löb shape)</summary>

The `LogOS/Theorems/Meta/*` namespace contains assumption-based theorem schemas. Transport is via the canonical fold:

- Assumptions: `LogOS/Theorems/Meta/Assumptions/Core.agda`, `LogOS/Theorems/Meta/Assumptions/Diagonal.agda`
- Transport: `LogOS/Theorems/Meta/Full.agda`
- Wrappers: `LogOS/Theorems/Meta/Rice.agda`, `LogOS/Theorems/Meta/Tarski.agda`, `LogOS/Theorems/Meta/Godel.agda`, `LogOS/Theorems/Meta/Lob.agda`

</details>
