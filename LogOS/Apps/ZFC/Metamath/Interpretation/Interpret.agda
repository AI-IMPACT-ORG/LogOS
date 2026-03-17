{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.Interpretation.Interpret where

-- Interpret a parsed pipeline into a meta-free first-order formula (if possible),
-- then normalize vacuous binders introduced by closure.

open import LogOS.Prelude

open import LogOS.Apps.ZFC.Metamath.Core as Core using
  ( Maybe
  ; just
  ; _>>=_
  )

open import LogOS.Apps.ZFC.Metamath.SetMM.Syntax using (toFormula)

open import LogOS.Apps.ZFC.Proof.Syntax using (Formula)

open import LogOS.Apps.ZFC.Metamath.Interpretation.Pipeline using
  ( ConclPipeline
  ; parsedConcl
  )

open import LogOS.Apps.ZFC.Metamath.Interpretation.Normalize using
  ( dropVacuousQuantifiers )

interpretMetaFree : ConclPipeline → Maybe Formula
interpretMetaFree P =
  toFormula (parsedConcl P) >>= λ φ →
  just (dropVacuousQuantifiers φ)
