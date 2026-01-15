<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

Opacity Layout
==============

This directory contains the **Opacity** strand: observability ledgers, opacity/barrier
theorems, and application-facing wrappers.

Note: this repository previously had a GRH domain directory; the former “GRH strand”
is now presented as **Opacity**, with GRH kept as an explicit application surface.

Publication-facing entrypoints
------------------------------

- Narrative spine: `docs/Applications/Opacity.lagda.md`
- Curated model surface: `LogOS/Packs/Opacity/Experimental/Core.agda`

Core modules (this directory)
-----------------------------

- Narrative-first aggregator (core re-exports): `LogOS/Domain/Opacity/Core.agda`
- Vacuity / meaningfulness guards: `LogOS/Domain/Opacity/Meaningfulness.agda`
- Opacity/ledger primitives: `LogOS/Domain/Opacity/GRH.agda`, `LogOS/Domain/Opacity/SpectralPack.agda`
- Separation / barrier theorem surface: `LogOS/Domain/Opacity/TruthSeparation.agda`

GRH application surface
-----------------------

- Domain-level wrapper: `LogOS/Domain/Opacity/Applications/GRH.agda`
- Curated model wrapper: `LogOS/Packs/Opacity/Experimental/Applications/GRH.agda`

Build
-----

- Typecheck publication docs: `make docs` (from repo root)
- Typecheck CI surface: `make ci` (from repo root)

Notes
-----

- All GRH/RH-related claims are conditional: analytic input (explicit-formula/Weil
  direction, spectral bridges, completeness/coverage) is always encoded as explicit
  fields in records.
- If you want to phrase “spectral separation” as an output type, use
  `LogOS/Theorems/Meta/SpectralSeparationOutput.agda` (`SpectralSeparationOutput`,
  `HasSeparation`, `NoSeparation`).
