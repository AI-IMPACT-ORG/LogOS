{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.ZFC.Examples where

-- First-class ZFC instance artifact (textbook WFGraph route with explicit AC).
--
-- This packages a single assumptions record (which includes the explicit Choice
-- witness) into a reusable object exposing:
-- - derived pack/claim,
-- - LogicCore projection,
-- - ZFC assumption bundle.

open import LogOS.Prelude

open import LogOS.API.Assumptions.Core using (LogicCore)
import LogOS.Packs.Assumptions.ZFC as AssumpZFC
import LogOS.Packs.ZFC.WFGraph as WF

record TextbookWithChoiceInstance {ℓ : Level} : Set (lsuc (lsuc ℓ)) where
  field
    assumptions : WF.TextbookZFC.Assumptions {ℓ}

  pack : WF.TextbookZFC.Pack {ℓ}
  pack = WF.TextbookZFC.mkPack assumptions

  claim : WF.TextbookZFC.Claim assumptions
  claim = WF.TextbookZFC.claimOf pack

  core : LogicCore {ℓ}
  core = WF.TextbookZFC.Claim.core claim

  zfcBundle : AssumpZFC.ZFCBundle core
  zfcBundle = WF.TextbookZFC.Claim.zfcBundle claim

