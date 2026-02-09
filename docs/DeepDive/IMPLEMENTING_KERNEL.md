<!--
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Implementing a Kernel (checklist)

This file is kept as a DeepDive appendix-style checklist.
The maintained entrypoint is `docs/LogOS_Overview.lagda.md`.

The LogOS design is “hexagonal”: the Kernel is a small interface; everything else
(ZFC, complexity/physics of information, opacity/observability, universality/IR, agents) is an
application pack that *instantiates* the Kernel and proves additional structure.

Interpretation (analogy):
terms like “hexagonal” and “physics of information” are architecture/motivation labels.
All semantic strength comes only from the explicit interfaces/assumptions you instantiate.

## Minimal checklist

1. Pick the **domain of discourse** (your “world” of states/objects).
2. Instantiate the Kernel’s **truth layer** and its **regulated closure**
   (`Flow` in the current codebase) together with the required laws.
   Optional: if you want grade‑indexed closure, implement `LogOS/Kernel/Graded`
   and use the graded endomap DSL in `LogOS/Kernel/Graded/Endo.agda` (be explicit
   about the step‑grade vs saturation‑grade distinction; do not conflate them).
3. Provide the **code surface** (`Code`, `encode`, `decode`) and any required
   reflection/guard interface (so “steps” can be represented and checked).
4. Provide the **process composition layer** (the endomorphism DSL / “allowed
   steps”) and prove that composition is well-typed and respects the relevant
   congruence/transport laws.
5. If your kernel/application uses quantitative reasoning (time, resources,
   observability budgets), instantiate the **resource schema** and prove
   non-degeneracy/meaningfulness constraints (so the model can’t trivialize by
   choosing empty domains or impossible time predicates).

## Where to look (current docs)

- Architecture and entrypoints: `docs/LogOS_Overview.lagda.md`
- Formal spec (multi-institution view): `docs/Views/MultiInstitution.lagda.md`
- 3-level HoTT-style view (host-facing): `docs/Views/HomotopyTypeTheory.lagda.md`
