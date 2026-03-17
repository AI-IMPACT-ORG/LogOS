<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Path: programming language theory

Goal: read LogOS as a refinement-directed interface discipline for semantics,
translation, and tooling loops.

```agda
{-# OPTIONS --safe #-}
module docs.Interpretations.Paths.PLT where

import LogOS.API.LT
```

This is the maintained programming-language-theory route named from the
top-level README. It supersedes the older `PL` path.

1) Capstones
------------

- Overview + architecture pointer: `docs/Core/Orientation/LogOS_Overview.lagda.md`
- Design-target spec (kernel + architecture/implementation/facade split):
  `docs/Core/Spec/LogicalTransformers.lagda.md`
- Refinement-first result spine: `docs/Results/Refinement_First_Results.lagda.md`
- Summit capstone route: `docs/Results/Summit.lagda.md`

2) Views
--------

- `docs/Interpretations/Views/Semantics_And_Observation.lagda.md`
  (decode-first discipline, explicit observation semantics, shared distributed
  semantics)
- `docs/Interpretations/Views/Logic_Programming_And_Type_Theory.lagda.md`
  (programming-theory, derivability, proof-theory, and type-theory overlays)
- `docs/Interpretations/Views/Mathematics_And_Completion.lagda.md`
  (sigma-directed completeness, `run` summaries, and fixed-point spines)
- Two kernel "tooling loop" theorems:
  `LogOS/LT/Theorems/Effectivisation.agda`,
  `LogOS/LT/Theorems/StableCompletion.agda`
- Reflective-image effectivity / weakest-precondition reading:
  `LogOS/LT/Theorems/AbstractGaloisConnection.agda`,
  `LogOS/Ports/Residuals.agda`
- Observation-induced partiality as canonical extensional semantics, with
  fixed-observation complete presentations centered on the canonical induced
  extensional semantics:
  `docs/Patterns/Partiality_Through_Observation.lagda.md`
- Critical-budget agreement for universality:
  `LogOS/Apps/Universality/Agreement/Universal.agda`
- Flagship stacked-transformer universality architecture façade:
  `LogOS/Apps/Universality/Architecture.agda`
- Apps-side capstone route:
  `LogOS/Apps/Summit/All.agda`
- Strong downstream mechanisability and its direct consequence functions:
  `LogOS/Apps/Summit/Mechanisable.agda`,
  `LogOS/Apps/Summit/Theorem.agda`
- Optional observational-sufficiency / no-backflow doctrine on recognised
  mechanisable images:
  `LogOS/Apps/Summit/Admissibility.agda`
- Local presentation independence over a fixed shared boundary, exposed as a
  symmetry/descent theorem on recognised mechanisable images:
  `LogOS/Apps/Summit/Theorem.agda`,
  `LogOS/Apps/LogicArchitecture/MetaTheory/Basis/ObservationReflection/Core.agda`
- Package-level local symmetry over one recognised image and one fixed
  mechanisable payload, where comparison is induced by the common boundary
  presentation:
  `LogOS/Apps/Summit/Theorem.agda`

3) One concrete pack
--------------------

- Turing-category bridge (observation-induced partiality): `LogOS/Apps/TuringCategory/All.agda`
- Concurrency (happens-before closure example): `LogOS/Apps/Concurrency/All.agda`

4) Build-your-own checklist
---------------------------

- Construction guide:
  `docs/Patterns/HowTo/HowTo_Build_Logic_Transformer_Architecture.lagda.md`
- Practical downstream guide:
  `docs/Patterns/HowTo/HowTo_Practical_Architecture_Tips.lagda.md`
