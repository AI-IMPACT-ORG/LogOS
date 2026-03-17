<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Audit guide (humans)

This page explains how to audit LogOS documentation against the checked code and executable policy.

```agda
{-# OPTIONS --safe #-}
module docs.Core.Orientation.Audit_Guide where

import LogOS.API.LT
```

## What is “auditable” here?

LogOS aims to be mechanically honest:

- All literate docs (`*.lagda.md`) are typechecked by `make check-docs` (via `scripts/check_all_docs.sh`).
- Architectural and hygiene rules are enforced by `make ci-policy` (see the generated index `docs/Generated/Policy_Index.md`).
- High-risk prose claims are stamped with explicit claim stamps (`docs/Core/Meta/Claim_Stamps.md`).
- Repository lane boundaries are documented in `docs/Core/Project/Repository_Contract.md`.
- Weak-semantics footguns are summarised in `docs/Core/Orientation/High_Risk_Conventions.lagda.md`.

Non-goal: prove every interpretation in prose. Interpretations are welcome, but must be labelled as such.

## The three sources of truth

1. **Agda code** (`LogOS/**`) — definitions and theorems.
2. **Typechecked specs** (`docs/Core/Spec/*.lagda.md`) — the design-target specification and repo-aligned claims.
3. **Executable policy** (`scripts/check/*.sh` + `make ci-policy`) — what the repo enforces.
4. **Repository contract** (`docs/Core/Project/Repository_Contract.md`) — which lanes are canonical, generated, policy-only, tooling-only, or historical.

## How to audit a claim stamp

A claim stamp has the form:

`<!-- CLAIM-STAMP: KIND | anchor=path#symbol -->`

Audit steps:

1. Open the referenced `path`.
2. Locate `symbol`:
   - in `*.agda` / `*.lagda.md`: the check treats it as a literal substring search.
   - in `*.md`: the check treats it as a markdown heading anchor (slugged).
   - in `*.tex`: the check treats it as a `\\label{symbol}`.
3. Confirm the surrounding content matches the intended claim:
   - **DEFINITION**: the repo defines this as stated.
   - **DERIVED**: there is a proof spine in code (or policy script) that establishes it.
   - **ASSUMPTION**: it is parameterised / explicitly assumed (not smuggled in).
   - **ANALOGY**: it is non-binding interpretation.
   - **PLANNED**: it is explicitly not implemented yet.

## Worked audit path (example)

Example: the overview page cites the repo’s architecture diagram as a definition stamp.

1. Start at: `docs/Core/Orientation/LogOS_Overview.lagda.md`.
2. Find a claim stamp that anchors into:
   `docs/Core/Architecture/Diagram.lagda.md#architecture-intended`.
3. Open that diagram doc and verify the heading/anchor exists and matches the prose reading.
4. If the claim is about enforcement, follow the pointers to:
   `scripts/check/layer_order_check.sh` and `docs/Generated/Policy_Index.md`.

## Commands for auditors

- Policy lane: `make check-policy`
- Core Agda lane: `make check-core`
- Integration Agda lane: `make check-integration`
- Docs lane: `make check-docs`
- Library smoke lane: `make check-lib`
- Cold umbrella gate: `make check-all`
- HTML build (spot-check rendered docs): `make html`

Navigation aids:

- Global docs index (generated): `docs/Generated/Docs_Index.md`
- Claim stamp index (generated): `docs/Generated/Claim_Stamp_Index.md`
- Module index (generated): `docs/Generated/Module_Index.md`
- Repository lane contract: `docs/Core/Project/Repository_Contract.md`
- High-risk conventions: `docs/Core/Orientation/High_Risk_Conventions.lagda.md`
