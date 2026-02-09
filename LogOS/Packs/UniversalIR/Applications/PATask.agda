{-
LogOS: a prototype Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Packs.UniversalIR.Applications.PATask where

-- Bundle the “one algorithm, many paradigms” construction as a standard quartet.

open import LogOS.UniversalIR.Theorems public
  using (Assumptions; Claim; Pack; mkPack; assumptionsOf; claimOf)

