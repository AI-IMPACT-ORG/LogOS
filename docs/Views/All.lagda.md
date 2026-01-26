<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Views — LogOS (One Kernel, Many Readings)

```agda
{-# OPTIONS --safe #-}
module docs.Views.All where

import docs.Views.MultiInstitution as MultiInstitution
import docs.Views.HoTT_3Level as HoTT_3Level
import docs.Views.CategoricalLogic as CategoricalLogic
import docs.Views.ObserverSemantics as ObserverSemantics
import docs.Views.CurryHowardLambek as CurryHowardLambek
import docs.Views.MeredithSentences as MeredithSentences
```

This folder contains a set of **semantic views**: mutually consistent readings
of the same kernel interfaces.

These views do not add logical power. They are documentation artefacts: each
view note is itself a typechecked Agda module (the top ` ```agda ` block), and
the prose around it is explanatory only.

Interpretation (analogy):
some view titles use interpretive labels for orientation (e.g. “physics-of-information”); the formal content is the Agda development in the imported view modules.

Views (entrypoints)
------------------
- Multi-institution (classic model theory): `docs/Views/MultiInstitution.lagda.md`
- 3-level HoTT-style positioning: `docs/Views/HoTT_3Level.lagda.md`
- Categorical logic (2-category view): `docs/Views/CategoricalLogic.lagda.md`
- Observer semantics (physics-of-information interpretation): `docs/Views/ObserverSemantics.lagda.md`
- Curry–Howard–Lambek capstone (proof/model/category/observer bundle): `docs/Views/CurryHowardLambek.lagda.md`
- Meredith sentences (ultra-compact LogicKernel/CHL core): `docs/Views/MeredithSentences.lagda.md`
