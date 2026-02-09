{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Assumptions.ZFC where

-- Math bundle: ZF/ZFC interfaces over the shared Kernel core.
--
-- Notes:
-- - The ZF/ZFC packs depend only on the kernel *shape* (code/decode), so we
--   state them over `LogicCore.KLike`.
-- - GRH lives in the Opacity domain and is intentionally kept orthogonal; see
--   `LogOS.Domain.Opacity.GRHLedger` for the separate GRH ledger.

open import LogOS.Prelude

open import LogOS.API.Assumptions.Core
open import LogOS.ZFC.SetTheory.Pack as SetTheory using (ZFAxioms; ZFCAxioms)

record ZFBundle {ℓ : Level} (C : LogicCore {ℓ}) : Set (lsuc (lsuc ℓ)) where
  field
    zf : ZFAxioms (LogicCore.KLike C)

record ZFCBundle {ℓ : Level} (C : LogicCore {ℓ}) : Set (lsuc (lsuc ℓ)) where
  field
    zfc : ZFCAxioms (LogicCore.KLike C)

  zf : ZFAxioms (LogicCore.KLike C)
  zf = ZFCAxioms.zf zfc
