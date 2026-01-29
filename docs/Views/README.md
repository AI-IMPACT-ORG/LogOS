<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Views — One Kernel, Many Readings

Entry point:
- Views index (imports/typechecks all view notes): `docs/Views/All.lagda.md`

Each view note is a literate Agda document (`*.lagda.md`) and is itself
typechecked by `make docs`. The views are mutually consistent readings of the
same kernel interfaces; they do not add logical power.

Interpretation (analogy):
you can think of these as “SQL views” over a single underlying schema: each
document is a projection/adaptation of the same kernel interface into a
different vocabulary (institutional/model-theoretic, CHL, categorical logic,
etc.). The analogy is only meant to convey **derived presentations**: the formal
content is always the imported/typechecked Agda surfaces.

## Documentation contract (per view)

Each view note is expected to include, near the top:

- **Terminology conventions:** the canonical “literature ↔ LogOS” mapping lives
  in `docs/Terminology.lagda.md`.
- **Interpretation (analogy)**: a short guardrail statement clarifying that this
  is a derived presentation (“view”), and that any interpretive vocabulary is
  orientation only.
- **Scope (formal)**: what structure the view is parameterized by (e.g.
  `Kernel Sig Q`, `LogicKernel Sig Q`, or a minimal boundary structure).
- **Adapter mapping to literature**: a small “term ↔ identifier” table that lets
  a domain expert read LogOS as an explicit adapter of the familiar concept.
- **Assumptions (explicit)**: any extra hypotheses needed to upgrade the view
  from preorder/lax structure to a textbook-strength statement (e.g.
  antisymmetry, proof-irrelevance, ωCPO, adequacy/budgeted adequacy).
- **Residual / what is new here**: a short paragraph stating what LogOS does
  differently from the standard presentation (usually: preorder-first,
  laxness/irreversibility, explicit closure/truth-after-computation, explicit
  ports/adapters calculus).
- **Theorem spine (authoritative)**: paths/identifiers that are the formal
  claims this view is presenting (the prose is explanatory).
