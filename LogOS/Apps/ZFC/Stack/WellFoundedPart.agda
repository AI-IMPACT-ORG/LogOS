{-
  LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
  Copyright (C) 2026 AI.IMPACT GmbH
  SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.ZFC.Stack.WellFoundedPart where

-- Construct a “well-founded part” of a ZF base stack by restricting the
-- universe to sets equipped with an accessibility proof `Acc _∈_`.
--
-- This module is split into:
-- - `WellFoundedPart.Universe` : the restricted universe + induced membership,
-- - `WellFoundedPart.Closure`  : closure of `Acc` under base constructors,
-- - `WellFoundedPart.Lift`     : lifting a base stack into the restricted universe.

import LogOS.Apps.ZFC.Stack.WellFoundedPart.Lift as Lift
open Lift public
