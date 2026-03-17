{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Metamath.BiDirectional.RoundTrip where

-- Large proof module split into:
-- - `RoundTrip.ReifyInversion` : inversion lemmas for the reifier (`toPFormulaWithVars`),
-- - `RoundTrip.Main` : the renaming roundtrip statement
--   (`toFormulaRenamingRoundTrip`, with `toFormulaRoundTrip` kept as a
--   compatibility alias).

import LogOS.Apps.ZFC.Metamath.BiDirectional.RoundTrip.Main as Main
open Main public
