<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

GRH (Application Surface)
========================

This repository rebrands the former “GRH strand” as **Opacity**:

- Opacity core (observability ledgers + opacity/barrier theorems): `LogOS/Domain/Opacity/*`
- GRH wrappers as an application: `LogOS/Domain/Opacity/Applications/GRH/*`

Publication-facing entrypoints
------------------------------

- Narrative spine: `docs/Application_Opacity.lagda.md`
- Opacity model surface: `LogOS/Models/Opacity/Core.agda`
- GRH application surface: `LogOS/Models/Opacity/Applications/GRH.agda` and `LogOS/Domain/Opacity/Applications/GRH.agda`

Build
-----

- Typecheck GRH doc: `make docs` (from `agda_library_1.0/`)
- Typecheck full CI surface: `make ci` (from `agda_library_1.0/`)

Notes
-----

- All GRH-related claims are conditional: heavy analytic input (explicit-formula/Weil direction,
  spectral bridges, completeness/coverage) is always encoded as explicit fields in records.
- If you want to phrase “spectral separation” as an output type, use
  `LogOS/Theorems/Meta/SpectralSeparationOutput.agda` (`SpectralSeparationOutput`, `HasSeparation`, `NoSeparation`).
