<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# S03: Displayed structure (ports as displayed thin 2-categories)

Displayed structure is the primary mechanism LogOS uses to express *ports*:
extra configuration on objects and extra obligations on morphisms, without changing
the underlying notion of observable refinement.

```agda
{-# OPTIONS --safe #-}
module docs.Core.Textbook.Sections.S03_Displayed_Structure where

import LogOS.API.LT
```

## DisplayedThin2Cat (port shape)

A displayed thin 2-category over a base thin 2-category `C` consists of:

- displayed objects `Ob` over each base object,
- displayed morphisms `HomD` over each base morphism, relating displayed endpoints,
- displayed identity and composition operations (`idD`, `compD`).

In LogOS this is packaged as `DisplayedThin2Cat` in `LogOS/LT/DisplayedThin2Cat.agda`.

## Totalisation (Σ-decoration)

Given a displayed layer `D : DisplayedThin2Cat C … …`, totalisation yields a new
thin 2-category `DecoratedThin2Cat D` whose:

- objects are pairs `(baseObj , displayedObj)`,
- morphisms are pairs `(baseHom , displayedHom)`,
- refinements/2-cells are **inherited from the base** (displayed evidence does not affect `_⊑_`/`≈`).

This is the formal basis for the “weak coupling” discipline:
ports add obligations, while observable comparison stays on the base wiring.

## Products and stacks

Independent ports compose by product of displayed layers:

- `ProductDisplayed D₁ D₂` is a displayed layer carrying both payloads.

For n-ary composition, LogOS standardises the packaging via:

- `PortSig` (a displayed layer tagged by a type-level label),
- `PortStack` (right-associated product-stacking of `PortSig` entries),
- capability-driven projections and forgetting (`HasPort`, `getObj`, `getHom`, `forgetPort`, `forgetSubstack`).

The infrastructure lives in `LogOS/LT/Ports/PortSig.agda` and `LogOS/LT/Ports/PortStack.agda`.

Universe note:
port tags are universe-polymorphic (`Tag : Set ℓTag`), and the port infrastructure stores displayed
levels as data, so it is packaged in `Setω`.

## Strictness discipline

Displayed layers may also express explicit robustness checks (e.g. strict decode laws).
Any collapse from mutual refinement `≈` to equality `≡` is only available behind
explicit, opt-in ports/layers (never as ambient structure in the LT spine).
