<!--
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% ZFC Demo — derived ZF constructions

```agda
{-# OPTIONS --safe #-}
module docs.DeepDive.ZFC_Demo where

open import LogOS.Prelude

open import LogOS.Domain.ZFC.SetTheory.FormulaPack using (ZFAxiomsᶠ)
import LogOS.Domain.ZFC.SetTheory.FormulaDerived as FormulaDerived
import LogOS.Domain.ZFC.SetTheory.Dsl
import LogOS.Domain.ZFC.SetTheory.StageToCHFromHierarchy
import LogOS.Packs.ZFC.WFGraph as ZFCPack
```

This is a small, typechecked “proof-of-mechanisation” note: it shows how to do
recognisable ZF reasoning (singleton, binary union, membership equivalences)
*inside the coded/formula-pack interface* used by the WFGraph route.

For the forcing-like boundary closure (Flow/μFlow) that ties ZF back to the kernel,
see `LogOS/Domain/ZFC/SetTheory/Dsl.agda` and `LogOS/Domain/ZFC/SetTheory/StageToCHFromHierarchy.agda`.
This demo stays strictly inside the formula-pack surface.

## Minimal derived constructions (formula-pack ZF)

```agda
module _ {ℓ : Level}
         (W : ZFCPack.WFGraphStructure ℓ)
         where

  module Z = ZFCPack.ZFᶠ
  A : Z.Assumptions {ℓ}
  A = record { W = W }

  P : Z.Pack {ℓ}
  P = Z.mkPack A

  open Z.Pack P
  open Z.Claim claim
  open ZFAxiomsᶠ zfᶠ

  module Der = FormulaDerived.For K zfᶠ
  open Der public using (singleton; mem-singleton↔; union₂; mem-union₂↔)

  hp = P
```
