<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# View family: Semantics and Observation

```agda
{-# OPTIONS --safe #-}
module docs.Interpretations.Views.Semantics_And_Observation where

import LogOS.API.LT
```

This umbrella view collapses the earlier observer-semantics, formal-semantics,
formal-languages, and shared-distributed-semantics notes into one reader-facing
surface.

What is actually defined
------------------------

- **Observer semantics**: explicit observation interfaces (`View`), kernel
  readouts (`decode`), boundary-driven refinement, probe-suite/locality
  machinery, and optional opacity tooling.
- **Formal semantics**: semantics by explicit readout plus the canonical
  pullback refinement induced by that readout; optional presentation layers can
  justify alternative derivation interfaces for the same semantics, both for
  single views and for probe suites.
<!-- CLAIM-STAMP: DERIVED | anchor=LogOS/LT/Presentation/Independence.agda#presentationsAgree -->
- **Presentation independence**: any complete presentation over one fixed
  observation view or suite agrees with the canonical pullback refinement, so
  the observation boundary remains the semantic anchor.
- **Formal languages**: a code carrier `Code`, a semantics map `decode`, and
  translations judged by boundary behaviour rather than by syntax alone, with
  proof systems transportable along meaning-preserving translations.
- **Shared distributed semantics**: locality-indexed boundaries, pointwise
  closure transport, and optional reversibility/cost layers stacked as explicit
  ports.

Literature reading
------------------

- **Observer semantics**: meaning is what the chosen boundary can distinguish.
- **Formal semantics**: semantics is explicit and presentation-dependent,
  rather than ambient.
- **Formal languages**: kernels can be read as language presentations equipped
  with an observed semantics and semantics-aware translations.
- **Shared distributed semantics**: fix one distributed boundary/doctrine, then
  study translations that preserve that shared semantics.

Where LogOS is weaker or more general
-------------------------------------

- observers are constraint preorders, not necessarily measurements in any
  physical sense;
- semantics is preorder-valued rather than truth-valued or set-valued by
  default;
- there is no fixed syntax class such as grammars, automata, or rewriting
  systems in the spine;
- “physical” or “distributed” meaning comes from explicit locality/closure
  data, not from a kernel primitive.

What is not claimed
-------------------

- no hidden observer-independent semantics in the spine;
- no universal operational/denotational equivalence theorem;
- no built-in parsing, grammar normal forms, or Chomsky-style hierarchy;
- no primitive physical ontology or guarantee that a shared distributed
  semantics stack corresponds to actual physics.

Code anchors
------------

- `LogOS/LT/View.agda`
- `LogOS/LT/Kernel.agda`
- `LogOS/LT/Hom.agda`
- `LogOS/LT/Presentation.agda`
- `LogOS/LT/Presentation/ObservationInitiality.agda`
- `LogOS/LT/Presentation/Interlingua.agda`
- `LogOS/LT/Presentation/Independence.agda`
- `LogOS/Ports/Locality/Core.agda`
- `LogOS/LT/Theorems/ProbeSuiteRepresentation.agda`
- `LogOS/Ports/PhysicalSemantics/Core.agda`
- `docs/Patterns/Shared_Distributed_Semantics.lagda.md`
