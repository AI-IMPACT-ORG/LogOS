<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

# Design decision: guarded Lawvere

```agda
{-# OPTIONS --safe #-}
module docs.Patterns.Guarded_Lawvere where

import LogOS.API.LT
import LogOS.API.Reification
import LogOS.Apps.ZFC.Stack.AsymptoticReification
```

This note records the first Lawvere-adjacent theorem layer added to the
optional reification surface over the LT spine.

## Design choice

The library does **not** import classical Lawvere diagonal arguments as raw
fixed-point principles.

Instead it uses a guarded, refinement-first variant:

- observations are named explicitly,
- fixed points live on stable points of a chosen `Flow`,
- equality is replaced by `≈`,
- failure of fixed points is stated as an explicit obstruction.

This keeps the theorem aligned with the rest of LogOS:

- observation-first,
- closure-guarded,
- refinement-first,
- assumption-scoped.

## What is defined

- `LogOS.Ports.Reification.GuardedLawvere`
  - `StableEvaluator`
  - `QuotedPointSurjective`
  - `lawvereStableFixedPoint`
  - `noStableFixedPoint-obstructsQuotedPointSurjective`

- `LogOS.Apps.ZFC.Stack.AsymptoticReification.GuardedLawvere`
  - `FlowCollapse`
  - `totalPredicateReification→QuotedPointSurjective`
  - `diagonalNoFixedPoint-obstructsTotalPredicateReification`

## Reading

The generic theorem says:

- if stable observations can be quoted densely enough,
- then every stable endomap has a stable fixed point up to `≈`.

The ZFC specialization is deliberately more honest than a slogan:

- total predicate reification only names `Flow`-normalised predicates directly,
- so the concrete point-surjectivity result requires an explicit `FlowCollapse`
  witness,
- and the diagonal obstruction is therefore stated against
  `TotalPredicateReification + FlowCollapse`, not as an ambient theorem of
  incompleteness.

## What is not claimed

- this is **not** a full Gödel incompleteness theorem,
- this is **not** a full Tarski undefinability theorem,
- this is **not** unrestricted classical Lawvere,
- this does **not** identify thermodynamic irreversibility with logical
  incompleteness.

What it does provide is the reusable obstruction schema:

- sufficient quoted naming of stable observations forces fixed points,
- so a chosen no-fixed-point diagonal blocks that naming discipline.
