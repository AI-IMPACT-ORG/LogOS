{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.Agents.Comparisons.Cost where

open import LogOS.Prelude

-- Cost-aware comparisons (budget transport) are provided by `SchemeCategory`.

open import LogOS.Computation.SchemeCategory public
  using
    ( Process
    ; Interface
    ; schemeFromInterface
    ; ProcessHom
    ; ProcessHomLax
    ; ProcessHomCost
    )
