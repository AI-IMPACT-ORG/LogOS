<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Architecture view: the “bi‑pyramid” face {#architecture-bipyramid}

This document now describes the **derived construction/discipline face** of the
primary tetrahedral architecture package.
It is still a view only: no new axioms, no new semantic layer.

```agda
{-# OPTIONS --safe #-}
module docs.Core.Architecture.BiPyramid where

-- Sync guard: public docs should prefer the curated API surface.
import LogOS.API.LT
import LogOS.API.Architecture
```

## Status

The primary typed package is now:

- `LogOS.LT.Architecture.Tetrahedron.Tetrahedron`

The bi-pyramid is the derived face:

- `bipyramidFace = construction + discipline`

The canonical LT instance remains:

- equator: `LOG`
- construction apex: stacks reindexed by `stackKernel`
- discipline apex: `LOGᴳʳ` with weakening `toLOG`

Code anchors:

- primary package: `LogOS/LT/Architecture/Tetrahedron.agda`
- face view: `LogOS/LT/Architecture/BiPyramid.agda`
- canonical LT instance: `LogOS/LT/Architecture/LogOS.agda`

Pedantic boundary:
the bi-pyramid remains a useful view because many packs still live on this
face, but it is no longer the whole typed architecture story. The shared-boundary
realisation corner is part of the same package and is documented in:

- `docs/Core/Architecture/Tetrahedron.lagda.md`
