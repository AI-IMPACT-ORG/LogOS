<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Path: mathematics

Goal: read LogOS as a clean mathematical object with explicit "what is
assumed vs proved".

```agda
{-# OPTIONS --safe #-}
module docs.Interpretations.Paths.Mathematics where

import LogOS.API.LT
```

This is the maintained mathematics-facing route named from the top-level
README. It supersedes the older `Mathematician` path.

1) Capstones
------------

- Pure spec (definitions + theorem spine): `docs/Core/Spec/LogicalTransformers.lagda.md`
- Repo-aligned spec (what is and is not claimed): `docs/Core/Spec/LogOS_Specification.lagda.md`
- Result spine: `docs/Results/Refinement_First_Results.lagda.md`
- Assumptions ledger (what is explicit, not ambient): `docs/Core/Meta/Assumptions_Ledger.md`
- Terminology clarification (displayed vs fibrations; institution fragment /
  predicate reindexing fragment):
  `docs/Patterns/Clarifications/Displayed_Structure_vs_Fibrations.lagda.md`

2) Views (choose 1-2)
---------------------

- `docs/Interpretations/Views/Mathematics_And_Completion.lagda.md`
  (category theory, locales/nuclei, residuals, and sigma-directed completeness
  in one place)
- `docs/Interpretations/Views/Logic_Programming_And_Type_Theory.lagda.md`
  (Curry-Howard-Lambek bridge, institution fragment, derivability, and
  directed type-theory reading)
- `LogOS/Ports/Valuation/AbstractQuanticNucleus.agda`
  and `LogOS/Ports/Valuation/AbstractConnesKreimer.agda`
  (least stable multiplicative approximation, stable convolution, and
  renormalised convolution as its boundary-facing readout)
- Two "inevitability" theorems (representation + closure-gated self reference):
  `LogOS/LT/Theorems/ProbeSuiteRepresentation.agda`,
  `LogOS/LT/Theorems/StableCompletion.agda`

3) One concrete pack
--------------------

- Shared-boundary realisations pattern:
  `LogOS/Ports/Realisations/DependentStack.agda`
  and `LogOS/Ports/Realisations/Architecture.agda`
- ZFC construction (relative build from WF graphs): `LogOS/Apps/ZFC/All.agda`
