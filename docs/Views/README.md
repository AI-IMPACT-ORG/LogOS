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

Each view note is expected to include, near the top, enough content for a domain
expert to read it as an explicit **adapter note** to the literature, while
keeping LogOS-native boilerplate (tier bookkeeping, μ hypotheses, equality vs
refinement discipline) centralized in shared anchors.

- **Purpose:** what object/idea in the literature this view is presenting, and
  what it intentionally does *not* claim.
- **Notation (short):** the minimal local notation used in the view
  (refinement/equality/μ); for the canonical repository-wide conventions see
  `docs/Terminology.lagda.md` and `docs/Kernel/ClaimRegister.lagda.md`.
- **Dictionary (literature ↔ LogOS):** a compact mapping table (≈5–15 entries)
  from standard domain terms/notation to concrete LogOS identifiers.
- **Core definitions (literature style):** a small set of definitions stated in
  conventional mathematical language first, then immediately grounded in the
  exact LogOS definitions/records.
- **Theorem spine (authoritative):** the exact Agda surfaces this view is
  presenting (the prose is explanatory).
- **Residual vs literature:** what matches, what is weaker/lax, what ports/adapters
  add, and what is explicitly assumption-scoped.
- **Micro-example/diagram:** one worked mini-pattern (commuting square, inference
  rule, closure transport, etc.) that makes the view “feel real” without
  duplicating proofs.

Some views are intentionally ultra-compact (e.g. Meredith sentences): the goal
is still the same—an expert-facing adapter note with checkable anchors—just
without reintroducing boilerplate that already lives in the shared terminology
and claim register.
