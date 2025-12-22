<!--
LogOS: an Agda Library for foundational logic architecture
Copyright (C) 2025 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-->

% ZFC Demo — derived ZF constructions

```agda
{-# OPTIONS --safe #-}
module docs.ZFC_Demo where

open import LogOS.Prelude

open import LogOS.Domain.SetTheory.FormulaPack using (ZFAxiomsᶠ)
import LogOS.Domain.SetTheory.FormulaDerived as FormulaDerived
import LogOS.Packs.ZFC.WFGraph as ZFCPack
```

This is a small, typechecked “proof-of-mechanisation” note: it shows how to do
recognisable ZF reasoning (singleton, binary union, membership equivalences)
*inside the coded/formula-pack interface* used by the WFGraph route.

## Minimal derived constructions (formula-pack ZF)

```agda
module _ {ℓ : Level}
         (W : ZFCPack.WFGraphStructure ℓ)
         where

  module Z = ZFCPack.ZFᶠ
  A : Z.Assumptions {ℓ}
  A = record { W = W }

  P : Z.Pack A
  P = Z.mkPack A

  open Z.Pack P
  open ZFAxiomsᶠ zfᶠ

  module Der = FormulaDerived.For K zfᶠ
  open Der public using (singleton; mem-singleton↔; union₂; mem-union₂↔)

  hp = P
```
