<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# mmc

## Purpose

Small repo-local Haskell compiler/exporter for Metamath artifacts.

## Dependencies

- `ghc`
- repo script: `scripts/metamath/mmc_build.sh`

## Smoke test

- `bash scripts/metamath/mmc_smoke.sh`

## Outputs

- built executable: `_build/metamath/mmc/mmc`
- smoke artifact directory: `_build/metamath/mini_art`
