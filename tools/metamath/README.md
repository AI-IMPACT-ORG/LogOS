<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Metamath tools

## Purpose

Repo-local tooling for the Metamath ingestion pipeline used by the ZFC and
roundtrip examples.

This `tools/metamath/**` subtree is the canonical optional tooling entrypoint.
The parallel `scripts/metamath/**` subtree only provides wrapper commands and
smoke helpers for this tooling.

## Dependencies

- Python 3 for `tools/metamath/parse_mm/**`
- GHC for `tools/metamath/mmc/**`
- the helper scripts under `scripts/metamath/**`

## Smoke test

- `bash scripts/metamath/parse_mm_smoke.sh`
- `bash scripts/metamath/mmc_smoke.sh`

For the artifact contract and wrapper usage, see
`scripts/metamath/ARTIFACT.md`.

## Outputs

- parser smoke output: `_build/metamath/mini.mm.json`
- `mmc` smoke outputs: `_build/metamath/mmc/mmc` and `_build/metamath/mini_art/**`
