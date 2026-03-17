<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Claim stamps (documentation discipline)

LogOS docs aim for **extreme scientific honesty**: it must be clear which statements are:

- definitional (by unpacking types/records),
- derived (proved from definitions),
- assumptions (explicit additional inputs),
- analogies (interpretations, not theorems),
- planned (in the design-target spec, not yet mechanised).

To make this explicit in prose, we use lightweight *claim stamps* as HTML comments.

## Claim stamp format (CNL-lite)

Place a stamp **immediately before** the claim it classifies:

`<!-- CLAIM-STAMP: KIND | anchor=path#symbol -->`

Where:

- `KIND ∈ {DEFINITION, DERIVED, ASSUMPTION, ANALOGY, PLANNED}`
- `anchor=...` points to the primary code/prose anchor for the claim:
  - prefer an Agda definition/record in `LogOS/**/*.agda`
  - otherwise anchor to a doc section (e.g. `docs/*.md`, `Makefile`)

The anchor is repo-relative and must contain a `#` suffix (a symbol/section label).

## Examples (one per kind)

<!-- CLAIM-STAMP: DEFINITION | anchor=LogOS/LT/Kernel.agda#Kernel -->

<!-- CLAIM-STAMP: DERIVED | anchor=LogOS/LT/Presentation/ExtensionalMinimality.agda#mapCode-mono -->

<!-- CLAIM-STAMP: ASSUMPTION | anchor=LogOS/LT/Sup/AbstractSigmaDCPO.agda#SigmaDCPO -->

<!-- CLAIM-STAMP: ANALOGY | anchor=docs/Core/Orientation/Ontology.lagda.md#analogy-pointers-non-binding -->

<!-- CLAIM-STAMP: PLANNED | anchor=docs/Core/Spec/Implementation_Map.lagda.md#docs.Core.Spec.Implementation_Map -->
