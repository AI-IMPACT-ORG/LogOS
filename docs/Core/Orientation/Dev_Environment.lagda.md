<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Dev Environment (v1.1)

This note records the development toolchain expected by the LogOS policy gates.
It is intended to make “run the same checks as CI” straightforward for new contributors.

```agda
{-# OPTIONS --safe #-}
module docs.Core.Orientation.Dev_Environment where

-- Sync guard: public docs should prefer the curated API surface.
import LogOS.API.LT
```

What the policy expects
-----------------------

LogOS v1.1 relies on:

- **Agda** typechecking under strict flags (`--no-libraries`, `--safe`,
  `--without-K`, warnings as errors).
- **Repository policy tooling** under `scripts/check/*.sh` (shell tooling + Python scripts).

The default check surface is:

- `make check-policy`
- `make check-core`
- `make check-integration`
- `make check-docs`
- `make check-lib`
- `make check-all` as the clean umbrella gate
- `make check-all-warm` as the warm analogue of that same telemetry-backed full lane

Toolchain checklist
-------------------

Required tools:

- `agda`
- `python3`
- `rg` (ripgrep)
- `shellcheck`
- `make`

Optional tools:

- `ghc` + `cabal` (only if you build the Metamath helper under `tools/metamath/mmc`)

Quick verification (POSIX shell)
--------------------------------

```sh
# verify tool availability
command -v agda
command -v python3
command -v rg
command -v shellcheck
command -v make

# print versions + gate reminders
make toolchain-check
# (equivalently: bash scripts/check_env.sh)

# run the standard lanes
make check-policy
make check-core
make check-integration
make check-docs
make check-lib

# warm lanes for local iteration (no clean)
make check-core-warm
make check-all-warm

# or run the full clean umbrella gate
make check-all

# AI/LLM-assisted hand-off gate
make check-all
```

Known-good versions
-------------------

For a concrete reference, see:

- [KNOWN_GOOD_VERSIONS.md](../../../tools/dev/KNOWN_GOOD_VERSIONS.md)

Agda library entrypoint sanity
------------------------------

The canonical curated API smoke surface is:

- `LogOS/API/LT.agda`

If you want to use [LogOS.agda-lib](../../../LogOS.agda-lib) without registering
it globally, point Agda at an explicit library file:

- `LogOS/API/LT.agda`

For example:

```sh
mkdir -p _build
printf '%s\n' "$PWD/LogOS.agda-lib" > _build/local.agda-libraries
agda --no-default-libraries --library-file=_build/local.agda-libraries -l LogOS-LT --safe --without-K -W all -W error LogOS/API/LT.agda
```

If you have already registered the library with Agda globally, the shorter form
also works:

```sh
agda -l LogOS-LT --safe --without-K -W all -W error LogOS/API/LT.agda
```

`LogOS/API/Minimal.agda` remains available as a smaller downstream starter
surface, but `LogOS/API/LT.agda` is the repository's canonical curated API
entrypoint and the one mirrored by `make check-lib`.
