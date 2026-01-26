{-
LogOS: models for AI-driven, human-on-the-loop, machine-checked formal reasoning
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Comparisons.Refinement where

open import LogOS.Prelude

-- Comparisons are mediated by the existing SchemeCategory morphisms:
-- strict/lax process morphisms, cost-carrying morphisms, and induced scheme maps.

open import LogOS.Computation.SchemeCategory public
  using
    ( Process
    ; Choice
    ; schemeFromChoice
    ; ProcessHom
    ; ProcessHomLax
    ; ProcessHomCost
    ; ProcessHom→Lax
    ; idProcessHomLax
    ; _∘ProcessHomLax_
    ; mapChoice
    ; mapChoiceLax
    )
