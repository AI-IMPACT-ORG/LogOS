<!--
LogOS: an Agda research library for foundational logic system architecture.
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Contributing to LogOS (Agda Library)

Thanks for considering a contribution.

## Contributor License Agreement (CLA)

This repository accepts contributions only under an appropriate CLA, but the CLA process is handled out-of-band.

Please contact the author/maintainer for current CLA instructions before submitting a pull request.

## Checks

Run:

```sh
make ci
make lint
```

Optional (heaviest publication sanity):

```sh
make check-all
```

## Invariants (what CI enforces)

- No direct `Agda.Builtin.*` / `Agda.Primitive` imports outside the host-surface shims (see `README.md` “Host surface”).
- No `postulate` in the production library (`LogOS/*`, `Tests/*`); any assumptions must be explicit record fields.
- No `postulate` (and no unsafe OPTIONS) inside Agda code blocks in `docs/*.lagda.md`.
- Architectural layering: core layers must not import `LogOS.Domain.*` / `LogOS.Packs.*` / `LogOS.ObjectLogic.*` / `LogOS.Docs.*` (enforced by `scripts/import_layer_check.sh`).
- Prefer importing `LogOS.Prelude` / `LogOS.API.Minimal` instead of raw `Data.*`.
- Documentation path references inside backticks must resolve (see `scripts/doc_reference_check.sh`).

## Style (lemma names and shapes)

The library is curated for publication and aims to read like standard math.

- Prefer **aliases** over disruptive renames: if a lemma already has downstream users, keep it and add a textbook-name alias (e.g. Park/Kleene/Scott) rather than renaming the original identifier.
- Keep “operation vs laws” separated: add new assumptions as record fields, and add laws in dedicated theorem modules (avoid smuggling assumptions through imports).
- Use consistent naming for common proof patterns:
  - `mono-*` for monotonicity lemmas.
  - `*-assoc`, `*-idl`, `*-idr` for associativity and unit laws.
  - `*-cong` / `map-*` for congruence/naturality style lemmas (state the commuting diagram explicitly).
  - Prefer “surface” names on curated entrypoints (`LogOS.Theorems.Core`, `LogOS.API.Minimal`) and keep internal helper names local.
