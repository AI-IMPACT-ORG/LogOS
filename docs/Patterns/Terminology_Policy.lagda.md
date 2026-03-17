<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Design decision: terminology policy

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Terminology_Policy where

import LogOS.API.LT
```

This page records the curated outward-facing terminology for v1.1.
Rule of thumb: describe the mechanised structure first, and introduce literature
readings only as optional interpretations.
Use `docs/Core/Orientation/Ontology.lagda.md` for the broader glossary; this
page only fixes short outward-facing glosses for overloaded code names.

See also:

- `docs/Core/Orientation/High_Risk_Conventions.lagda.md`
- `docs/Patterns/Clarifications/Weak_vs_Strict_KernelHom.lagda.md`

Notation policy:

- Keep `_⊑_` as the primitive refinement relation in definitions.
- Use `≼` only as a public-facing alias for that same refinement relation when the order direction is easy to misread.
- Reserve plain `≤` for genuinely quantitative orders such as budgets, scales, or time.

| Code name | Curated prose | Allowed claims | Forbidden claims | Canonical anchors |
| --- | --- | --- | --- | --- |
| `Thin2Cat` | locally preordered 2-category | homs are preorders of 1-cells; 2-cells are refinement witnesses | proof-irrelevant bicategory by default | `LogOS/LT/Thin2Cat.agda` |
| `KernelHom` | boundary transport plus displayed implementation | `KernelHom = Σ BoundaryHom (BoundaryImplementation approx)`; decode coherence is `≈` by default | ambient strict equality of semantics | `LogOS/LT/Hom.agda`, `LogOS/LT/BoundaryHom.agda`, `LogOS/LT/BoundaryImplementation.agda`, `LogOS/LT/Coherence.agda` |
| `ObservedCodePreorder` | decode-induced observational preorder | comparison is the pullback of boundary refinement along `decode` | primitive operational preorder by default | `LogOS/LT/Kernel.agda` |
| `ClassicalLimit` | antisymmetry-based strictification | explicit collapse from `≈` to `≡` under an antisymmetry assumption | classical logic or physical classical mechanics by default | `LogOS/Ports/ClassicalLimit.agda`, `LogOS/LT/LOG/ClassicalLimit2Cat.agda` |
| `DependentLocalSemantics` | shared distributed semantics pack | explicit choice of locality index, local observables, and local closure family | built-in physical ontology | `LogOS/Ports/PhysicalSemantics/Core.agda` |
| `PhysicalTransformers` | shared distributed-semantics tooling | pointwise boundary transport plus closure preservation on a shared boundary | full physical semantics theorem | `LogOS/Ports/PhysicalTransformers.agda` |
| `LandauerAssumptions` | cost-law port | explicit grading/cost assignment with refinement-first laws | thermodynamic entropy/energy law by default | `LogOS/Ports/AbstractLandauer/Ledger.agda` |
| `CTDLedger` | universality ledger (CTD-style reading) | explicit universal kernel plus flow-preserving simulations into it | the full Church-Turing-Deutsch principle | `LogOS/Ports/Universality/CTD/Ledger.agda` |
| `QAdapter` | valuation algebra / quantitative adapter | finite-join prequantale-style scale with optional time presentation | canonical or physically privileged numeric semantics | `LogOS/Ports/Valuation/QAdapter.agda` |
| `LocalReversibility` | order-theoretic local reversibility | monotone endomaps with monotone inverses up to `≈` | unitarity or strict invertibility | `LogOS/LT/ConPreorder/Isomorphism.agda` |
| `PreQuantum` | prequantum / CQM-style layer | optional monoidal/discard/purification layers over a chosen base | Hilbert-space quantum mechanics in the spine | `LogOS/Ports/PreQuantum/*.agda` |

Use the stronger literature words only when the sentence also states the missing
assumptions or the exact fragment being implemented.
