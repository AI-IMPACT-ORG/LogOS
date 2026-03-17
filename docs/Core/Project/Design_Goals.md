<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Design goals (LogOS LT)

[Back to docs hub](../README.md)

This file is the surviving project-level narrative entrypoint.
It records repo intent, non-goals, and the roadmapped surface without keeping a
separate project README.

Entry points:

- Core: [`docs/Core/README.md`](../README.md)
- Results: [`docs/Results/README.md`](../../Results/README.md)
- Patterns: [`docs/Patterns/README.md`](../../Patterns/README.md)
- Interpretations: [`docs/Interpretations/README.md`](../../Interpretations/README.md)

Related:

- Typechecked spec: [`docs/Core/Spec/LogicalTransformers.lagda.md`](../Spec/LogicalTransformers.lagda.md)
- Archived TeX snapshots (optional), stored in a separate archive.

Goals
-----

- Minimal, expressive LT core.
- Refinement-first semantics with explicit boundaries.
- Explicit translation/adaptation as the primary engineering object.
- Host-minimal, stdlib-independent kernel.
- Auditability: docs trace to code.

Non-goals
---------

- Implicit axioms or hidden global assumptions.
- Hard dependency on Agda stdlib in the core.
- Treating apps/packs as part of the kernel.

Primary references
------------------

<!-- CLAIM-STAMP: DEFINITION | anchor=docs/Core/Spec/LogicalTransformers.lagda.md#docs.Core.Spec.LogicalTransformers -->

- Design-target spec: `docs/Core/Spec/LogicalTransformers.lagda.md`
- Mechanisation map: `docs/Core/Spec/Implementation_Map.lagda.md`
