{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.Bridge where

-- Bridge modules connecting the CH2008 partial-map/Turing-category pack to
-- Deutsch-style system categories in the LT spine.
--
-- v1.1 stance:
-- - These bridges are *structural* (functors, forgetful projections, Σ-packaging),
--   not claims of computational universality.
-- - Any meaning-changing step must be explicit (via `View`/boundary choice); we
--   do not silently identify “systems” with “partial maps”.
-- - Where we lift into `ParTracked`, that lift is parameterised by an explicit
--   CH2008 indexing ledger on `Par` (`ParTuringLedger`).
-- - The observation-program layer is a thin, inspectable surface over the same
--   explicit observation ports used by `KernelToPar`, not a second observation
--   semantics.

import LogOS.Apps.TuringCategory.Bridge.KernelToPar
import LogOS.Apps.TuringCategory.Bridge.AbstractDeutschToPar
import LogOS.Apps.TuringCategory.Bridge.ObservationPrograms
