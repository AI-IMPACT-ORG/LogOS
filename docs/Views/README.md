<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Views — One Kernel, Many Readings

Entry point:
- Views index (imports/typechecks all view notes): `docs/Views/All.lagda.md`

Each view note is a literate Agda document (`*.lagda.md`) and is itself
typechecked by `make docs`. The views are mutually consistent readings of the
same kernel interfaces; they do not add logical power.
