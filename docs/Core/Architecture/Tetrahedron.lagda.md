<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Architecture view: the tetrahedron {#architecture-tetrahedron}

This document gives the primary typed architecture reading for LogOS.
It is a **packaging view**, not a new axiom:
the underlying LT semantics are unchanged.

```agda
{-# OPTIONS --safe #-}
module docs.Core.Architecture.Tetrahedron where

import LogOS.API.LT
import LogOS.API.Architecture
```

## One equator, three forgetful apices

The shared equator is the preserved observational comparison world:

- `LOG`: kernels as objects, kernel morphisms as arrows, refinements as 2-cells.

The primary typed package is:

- `LogOS.LT.Architecture.Tetrahedron.Tetrahedron`

It packages:

- one **equator** thin 2-category,
- one **construction** apex,
- one **discipline** apex,
- one **realisation** apex,
- and forgetful functors from each apex back to the same equator.

The canonical LT-only construction/discipline instance lives in:

- `LogOS.LT.Architecture.LogOS`

The shared-boundary realisation corner lives in:

- `LogOS.Ports.Realisations.Architecture`

Pedantic boundary:
this package does not claim every downstream development must use exactly this
shape. It claims only that the repository’s canonical architecture story is
captured by this shape.

## The three apices

### Construction

The construction apex is presentation/program growth over one preserved
boundary:

- `Stack`
- `stackKernel`
- `programKernel`

This is the syntax-like direction: presentations, macro structure, and
same-boundary program transport.

### Discipline

The discipline apex is displayed growth over the architecture-first basis:

- `LOGᴳ`
- `LOGᴳʳ`
- `toLOG`
- displayed ports, laws, contracts, flow, quotation, and their totalisations.

This is the capability/law direction.

### Realisation

The realisation apex is the shared-boundary / many-realisations direction:

- `DependentLocalSemantics`
- `RealisationFamily`
- `LogOS.Ports.Realisations.Architecture.realisationApexOver`

This is the “one boundary, many code families realising it” corner.
Its canonical denotation surface into boundary-as-code is exported directly by:

- `DenoteK`
- `denoteOp`
- `denoteStack`
- `denoteProgram`

There is no extra ledger/deck wrapper on top of the chosen realisation family.

## Derived faces

The tetrahedron exports three named two-apex faces:

- `bipyramidFace`: construction + discipline
- `hexagonalFace`: discipline + realisation
- `sharedBoundaryFace`: construction + realisation

Interpretation:

- the old **bi-pyramid** reading is now the construction/discipline face,
- the **hexagonal** architecture reading is the discipline/realisation face
  over the same equator,
- the shared-boundary realisation story is not a parallel ad hoc architecture:
  it is a genuine apex in the same typed package.

## Refinement-first policy

All faces remain refinement-first:

- commuting claims are stated by `⊑` / `≈`,
- forgetful structure is functorial up to refinement,
- strict equality remains quarantined to explicit strictification or
  definitional bookkeeping lanes.

So the tetrahedron is a better package not because it adds power, but because
it states the existing architecture more honestly and with less duplication.
