<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Agda Code Hygiene (v1.1)

This guide is intentionally short. The authoritative hygiene rules are enforced by:

- `scripts/check/agda_hygiene_check.sh` (`make agda-hygiene-check`)
- `docs/Generated/Policy_Index.md` (search for `agda-hygiene-check`)

If you hit a hygiene failure, treat it as a refactor hint: make dependencies explicit, keep scopes local,
and split oversized modules rather than weakening checks.

Warnings policy
---------------

The build is intentionally strict:

- Agda is invoked with `-W all -W error` (see `Makefile`).
- Warning classes must not be silenced (no `-W no…` exceptions). If a warning fires, treat it as an avoidable signal.
- In particular, `CoverageNoExactSplit` is an Agda warning (“failed exact split checks”): refactor the offending
  definition so coverage splitting becomes exact instead of disabling the warning class.

When a warning appears, first confirm which Agda toolchain is in use:

- locally: `make agda-toolchain`
- CI: pinned via cabal (see `.github/workflows/ci.yml` + `.github/cabal-index-state.txt`)

Consistency checks (external libraries)
--------------------------------------

The default gate is **stdlib-free** (`--no-libraries`). Any external-library comparison must remain
non-load-bearing for the LogOS core:

- LogOS must not import external libraries.
- The external-library checks are generated under `_build/**` by their runner scripts and must be run explicitly.

Run:

- `make check_against_std_lib` (requires `AGDA_STDLIB`)
- `make check_against_cubical_lib` (requires `AGDA_CUBICAL_LIB`)

Adding a new external-library check:

1. Add a new runner script under `scripts/` modelled after `scripts/check_against_std_lib.sh`.
2. The runner should generate a downstream `*.agda` harness under `_build/Against<name>/**` and typecheck it with the
   required `-i` include paths.
3. Add a `make check_against_<name>` target that calls the script.
