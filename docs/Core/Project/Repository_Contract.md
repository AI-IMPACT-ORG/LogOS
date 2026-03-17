<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Repository contract

This repository distinguishes five lanes. They have different obligations and
must not silently bleed into one another.

## 1. Canonical authored surfaces

This is the maintained source-of-truth lane.

- `LogOS/**` except `LogOS/Checks/**`
- `docs/Core/**`
- `docs/Patterns/**`
- `docs/Interpretations/**`
- `docs/Results/**`
- top-level orientation files such as `/README.md`, `/AGENTS.md`, and `/Makefile`

Rules:

- These files define the live repository story.
- Public API modules under `LogOS/API/**` are for downstream conceptual use,
  not CI reachability plumbing.
- Legacy audience-split doc taxonomies are retired and must not reappear here.

## 2. Generated docs

These are committed derivative inventories and indexes.

- `docs/Generated/**`
- generated local indexes such as `docs/Patterns/All.lagda.md`
- generated local indexes such as `docs/Interpretations/Views/All.lagda.md`

Rules:

- Treat them as exhaustive lookup aids, not as the primary narrative.
- They must be regenerated from their scripts when the corresponding source
  inventory changes.

## 3. Policy and check roots

These files exist to enforce or witness repository invariants.

- `scripts/check/**`
- `scripts/gen/**`
- `scripts/lib/**`
- `.github/**`
- `LogOS/Checks/**`

Rules:

- Policy-only typecheck roots belong here rather than in curated API modules.
- If a check becomes part of the repository contract, it must be wired into
  `make ci-policy`.

## 4. Tooling and support

These files are support infrastructure around the formal library.

- `tools/**`
- `scripts/metamath/**`
- `tools/dev/**`

Rules:

- Tool subprojects must declare dependencies, outputs, and a smoke entrypoint.
- Build residue and interpreter caches are not part of the contract.

## 5. Historical archive

This lane is retained for provenance, not for the live development path.

Rules:

- Historical material is out of contract for the live repository and is stored in a separate archive.
- If archive material conflicts with canonical authored surfaces, canonical
  authored surfaces win.
