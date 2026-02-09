{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
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
    ; Interface
    ; schemeFromInterface
    ; ProcessHom
    ; ProcessHomLax
    ; ProcessHomCost
    ; ProcessHom→Lax
    ; idProcessHomLax
    ; _∘ProcessHomLax_
    ; mapInterface
    ; mapInterfaceLax
    )
