<!--
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% Metamath roundtrip contract

```agda
{-# OPTIONS --safe #-}
module docs.Interpretations.Applications.Metamath_Roundtrip where

open import LogOS.API.LT
import LogOS.Apps.ZFC.Metamath.BiDirectional as Bidir
import LogOS.Apps.ZFC.Metamath.Interpretation as Interp

reifyBoundary = Bidir.toPFormula
decodeBoundary = Bidir.toFormulaRenamingRoundTrip
emitBoundary = Bidir.toTokenEntryWithFrame
interpretBoundary = Interp.parseClosedConcl
```

This note states the semantic contract of the Set.MM roundtrip surface.

The important point is that the roundtrip is refinement-first, not
equality-first. There are three distinct boundaries:

- `Formula -> PFormula` is a partial reification step.
- `PFormula -> Formula` is certified only up to the environment-threaded
  renaming computed by the reifier and decoder.
- `Formula -> token row -> Formula` is exact only after the interpretation
  pipeline closes the conclusion under the mandatory frame's implicit outer `∀`
  and then drops vacuous binders introduced by that closure.

Support is explicit at emission time.

- `FormulaEntry.vars` is ambient support supplied before reification.
- `toTokenEntryWithFrame` also returns a `SupportFrame`, which separates:
  - `ambientVars`,
  - `binderVars`,
  - `mandatoryVars`.
- `TokenEntry.vars` is the normalized mandatory frame actually stored in the row
  and used to derive DB hypotheses.

What is proved
--------------

- The theorem exported as `toFormulaRenamingRoundTrip` states the decoder law
  at the `PFormula` boundary.
- The test module `LogOS/Apps/ZFC/Metamath/Tests.agda` checks row-level and
  DB-level emission/interpretation for closed formulas.
- The same test module also checks a representative partiality boundary:
  emission rejects `pairT`.

What is not claimed
-------------------

- no literal syntactic involution for binder token choices;
- no claim that every `Formula` has a Set.MM emission;
- no statement here that arbitrary imported `MM.Database` values are complete or
  faithful beyond the stated parser/closure/normalization pipeline.
