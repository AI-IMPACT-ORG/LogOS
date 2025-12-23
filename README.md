<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# LogOS (Agda) — a Logic Operating System

LogOS is an Agda library for foundational logic architecture that treats foundational logic as modern software. 

The library is espcially usefull using code assistants like Claude Code, Codex, Cursor or similar. An accompanying paper will appear soon on the arxiv.

It features small, host‑minimal kernel interface for a 3‑tier logic (S/H/G) with a reflective code surface, plus curated application packs (ZFC, complexity, universality/IR, opacity/GRH).

The main documentation can be found in the /docs folder. Uploading especially Definition_spec.lagda.md to any state-of-the-art reasoning chatbot instantiates a conversational interface to the library by using the chatbot as stochastic interpreter. Ensure memory features are switched off to avoid polluting memory. 


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
- ZFC story: `docs/Application_ZFC.lagda.md`, `docs/ZFC_Demo.lagda.md`
- Complexity story: `docs/Complexity.lagda.md`, `docs/Application_PvsNP.lagda.md`
- Universality story: `docs/Application_Universality.lagda.md`
- Opacity/GRH story: `docs/Application_Opacity.lagda.md`

HTML docs (Agda HTML backend):
- Build locally: `make html` → `_build/html/index.html`

## Entry Points

Recommended import surfaces:
- Minimal API: `LogOS/API/Minimal.agda`
- Core theorem surface: `LogOS/Theorems/Core.agda`
- ZFC: `LogOS/Packs/ZFC/All.agda` (WFGraph quartets: `LogOS/Packs/ZFC/WFGraph.agda`)
- Universality/IR: `LogOS/Models/Universality/Core.agda`, `LogOS/Models/UniversalIR/Core.agda` (bundle: `LogOS/Packs/Universality/All.agda`)
- Complexity: `LogOS/Models/Complexity/Core.agda`
- Opacity: `LogOS/Models/Opacity/Core.agda` (GRH application surface: `LogOS/Models/Opacity/Applications/GRH.agda`)

## Trust Boundary

- The safe core is intended to be imported via `LogOS/API/Minimal.agda` and contains no global postulates.
- Models that need ω‑chain suprema supply them explicitly via `LogOS/Axioms/OmegaSup/Interface.agda` (`ChainSup`) and `omegaCPO-from-chainSup`.

Host surface (portability):
- Direct imports from `Agda.Primitive` / `Agda.Builtin.*` are intentionally restricted to a small allowlist:
  - `Level.agda`
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
