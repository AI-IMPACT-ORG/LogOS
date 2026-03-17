<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Clarification: displayed structure vs (op)fibrations

This note is for readers who come in with standard category-theory expectations.
It pins down what LogOS *does* and *does not* mean by “thin 2-category”, “displayed”, and “Grothendieck”.

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Clarifications.Displayed_Structure_vs_Fibrations where

import LogOS.API.LT
```

## Thin 2-categories in LogOS

`Thin2Cat` (`LogOS/LT/Thin2Cat.agda`) is a *locally preordered 2-category*:

- objects are components/kernels/etc.
- for each `(A,B)`, the hom is a `ConPreorder` of 1-cells equipped with a refinement preorder `⊑`;
- 2-cells are literally refinement proofs in those hom-preorders.

The 2-category laws are stated **up to** mutual refinement `≈`, not as definitional equalities.
This matches the general repository stance: `⊑` is the primary judgment, `≈` is a derived equivalence, and `≡` is
used only for strict bookkeeping.

Code anchor: `Thin2Cat₂Cells` exposes the 2-cell vocabulary (identity, vertical composition, whiskering) as derived
structure inside the existing interface.

## Displayed structure in LogOS is *not* a fibration interface

`DisplayedThin2Cat` (`LogOS/LT/DisplayedThin2Cat.agda`) is “displayed-category style” packaging over a base thin
2-category `C`.

It is intentionally minimal and *engineering-driven*:

- displayed objects are per-component structure (ports/guards/doctrines),
- displayed morphisms are extra obligations on adapters,
- Σ-totalisation builds the “decorated component graph” (total objects and total morphisms),
- refinement between total morphisms is inherited **only** from the base 1-cells (no extra 2-cells introduced).

What is *not* modelled in v1.1:

- (op)fibration structure, cartesian/opcartesian lifts, or cleavages,
- any notion of “substitution by cartesian lifting”.

If you want that style of structure, it should be added explicitly as an additional port layer (and its obligations),
not assumed by reading “displayed” as “fibration”.

Code anchors:

- contracts as Σ-totalisation: `LogOS/LT/LOG/Contract2Cat.agda` (`LogOS.LT.LOG.Contract2Cat.WithPort`)
- flow layer as Σ-totalisation: `LogOS/LT/LOG/Flow2Cat.agda` (`LogOS.LT.LOG.Flow2Cat.WithPort`)
- encode layer as Σ-totalisation: `LogOS/LT/LOG/EncodePort2Cat.agda` (`LogOS.LT.LOG.EncodePort2Cat.WithPort`)

## Institution fragment / predicate reindexing are *minimal fragments*

The modules:

- `LogOS/LT/InstitutionFragment.agda`
- `LogOS/LT/PredicateReindexing.agda`

are *derived packaging* of existing kernel/contract structure.
They are intentionally conservative:

- the predicate-reindexing module is only the **reindexing** fragment (no quantifiers, no comprehension),
- the institution-fragment module records translations *covariantly* (matching the adapter/wiring reading).

For textbook contravariant “reducts/substitution”, take opposites at the appropriate level (see the notes in
`LogOS/LT/InstitutionFragment.agda` and `LogOS/LT/PredicateReindexing.agda`).

## Terminology invariants (public prose)

Use these phrases consistently in outward-facing docs:

- **observational refinement** (`_⇒∂_` in base `LOG`, `_⇒_` as an equivalent implementation-first view): pullback preorder along a boundary readout; compares only boundary images.
- **Σ-totalisation**: decorated objects/morphisms; refinement inherited from the base; displayed evidence ignored.
- **guarded closure / closure operator on a preorder**: idempotent up to mutual refinement (`≈`).
- **institution fragment / institution-style packaging**: covariant model transport by default (classical institution via opposite).
- **predicate reindexing fragment**: reindexing only, no quantifiers/comprehension.
- **finite-join prequantale**: join-prequantale in this repo; not a complete quantale.
- **σ/ω-directed completeness**: `SigmaDCPO` provides directed ω-suprema, not full dcpo.
- **(right) monoid action**: `step (t∙u) = step u ∘ step t`.
