<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% ZFC curated surface

This note is a regression guard for the public iterative-tree ZFC facade.

It imports the canonical slice/bridge surface and one explicit lower-rung
completion semantics leaf, then uses only the intended public names:

- `HierarchySectionᵛ`
- `Canonical.ForLevel`
- `Canonical.BridgeForLevel`
- `SemanticsCurrentCompletionSemantics.ForLevel`
- `BridgeSlice`
- `CompleteCurrent`

The split is intentional:

- `Canonical.ForLevel` is the canonical slice,
- `Canonical.BridgeForLevel` is the narrow theorem-facing instantiation of the
  generic successor-bridge names from
  `LogOS/Apps/ZFC/Stack/AsymptoticReification/SuccessorBridge.agda`,
- `SemanticsCurrentCompletionSemantics.ForLevel` is the explicit lower-rung
  optional completion semantics leaf.

Upgrade/assumption packaging is indexed separately in
`docs/Generated/ZFC_Upgrade_Index.md`.

```agda
{-# OPTIONS --safe #-}
module docs.Interpretations.Applications.ZFC_Curated_Surface where

open import LogOS.API.LT
import LogOS.Apps.ZFC.Models.IterativeSetTree.Semantics
```

This is intentionally narrow.

Its purpose is not to explain the mathematics. Its purpose is to point at the
canonical checked surface in
`LogOS.Apps.ZFC.Models.IterativeSetTree.Semantics.Curated`, while keeping
optional completion reachable only through an explicit leaf import.
