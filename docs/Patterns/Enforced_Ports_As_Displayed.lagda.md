<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Design decision: enforced ports-as-displayed discipline

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Enforced_Ports_As_Displayed where

open import LogOS.API.LT
```

This repo treats ports as *displayed structure* over a base thin 2-category, and
treats a “port category” as nothing more than the Σ-totalisation of that
displayed structure.

This is now also surfaced as part of the capstone theorem bundle:

- `LogOS/LT/Theorems/ArchitecturalNormalForm.agda`

There, the displayed discipline does not appear as an isolated design slogan.
It is one of the explicit fields of
`ObservationPreservingArchitecturalNormalForm`: the supported canonical LT
layers are exported as definitional displayed/totalised normal forms, and the
strictification layers are tracked separately as explicit late additions.

The discipline is made enforceable by compiling a small set of *definitional*
checks whose proofs are literally `refl`. If someone replaces a port 2-category
with a bespoke construction (or changes a port stack away from `ProductDisplayed`
with canonical projections), these checks stop typechecking.

The gate modules are:

- `LogOS/LT/LOG/Discipline/PortsAsDisplayed.agda` (canonical kernel-level ports)
- `LogOS/LT/LOG/Discipline/StrictificationAsDisplayed.agda` (explicit strictification law ports)
- `LogOS/Ports/Discipline/PortsAsDisplayed.agda` (canonical physical/budget/Deutsch ports)
- `LogOS/LT/Discipline/PortStackFolding.agda` (PortStack fold discipline)
- `LogOS/LT/Discipline/HomDefaults.agda` (kernel-hom default discipline)

CI also enforces *coverage* so no “straggler” `*2Cat.agda` modules silently bypass the discipline:

- `scripts/check/ports_as_displayed_coverage_check.sh` checks that every canonical `*2Cat.agda` module is imported
  by the corresponding canonical discipline gate.
- `scripts/check/ports_as_displayed_coverage_check.sh` is the canonical location of that check (wired into
  `make ports-as-displayed-coverage-check`).

This turns the discipline into a closed loop:

- the canonical gate modules enforce “ports are displayed + Σ-totalised” via definitional equalities,
- the strictification gate enforces the same invariant for explicit collapse-only law ports,
- the coverage check enforces that every port 2-category is routed through the appropriate gate.

The theorem-facing consequence is:

- `supportedArchitectureLayers` packages the canonical displayed/Σ-totalised LT
  spine;
- `supportedStrictificationLayers` packages the explicit collapse-only layers;
- the totalisation invariance facts (`total⊑→base⊑`, `base⊑→total⊑`,
  `total≈→base≈`, `base≈→total≈`) explain why displayed evidence enriches
  objects and morphisms without changing the 2-cell refinement order.

The curated API surfaces a single witness from each canonical gate so that
public-facing docs can stay on `LogOS.API.LT`:

```agda
_ : ⊤
_ = ltPortsAsDisplayed-ok

_ : ⊤
_ = ltPortStackFolding-ok

_ : ⊤
_ = ltHomDefaults-ok
```

The strictification gate remains explicit and separate under
`LogOS.API.Ports.LTStrictificationLOG`; its exported witness is
`ltStrictificationAsDisplayed-ok`. This note keeps the default doc surface
refinement-first instead of importing the strict lane by default.

The architecture-only sidecar witness remains available below the curated shell
in `LogOS.Ports.Discipline.PortsAsDisplayed.ArchitectureLaws`.

Sidecar: the Deutsch-style category is built from locality + causality + **local reversibility** (order-isomorphism),
and the no-cloning constraint is developed alongside it in:

- `LogOS/Ports/AbstractDeutschNoCloning.agda`
