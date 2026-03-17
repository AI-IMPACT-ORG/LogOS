<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Known-good tool versions (developer convenience)

This repository aims to be host-minimal and to typecheck under strict Agda flags (`--safe`, warnings as errors).
The CI policy checks also rely on a small toolchain (shell + Python tooling).

This file records versions that are known to work for LogOS v1.1, to make onboarding and debugging of CI
breakages more concrete.

Scope note:
- This is **not** a pinning mechanism by itself (it is a reference).
- If CI uses different versions, CI is the source of truth; update this file when that changes.

## Tested snapshot (2026-03-05)

Required:
- Agda: 2.8.0
- Python: 3.14.3
- ripgrep (`rg`): 15.1.0
- ShellCheck: 0.11.0

Optional (only for `tools/metamath/mmc`):
- GHC: 9.12.2
- cabal-install: 3.16.0.0

## Verify locally

Run:
- `bash scripts/check_env.sh`
- `make ci`
- `make check-all`

