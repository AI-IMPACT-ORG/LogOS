{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Irreversibility.All where

-- Irreversibility pack (obstructions + opacity-pack finite-loss examples).
--
-- Goal: collect small, explicit boundary-level examples where irreversibility
-- is witnessed directly inside the LogOS refinement discipline.
--
-- Entrypoints:
-- - `LogOS/Apps/Irreversibility/BitReset.agda`
-- - `LogOS/Apps/Irreversibility/BitResetDeutsch.agda`
-- - `LogOS/Apps/Irreversibility/BitResetCompression.agda`
-- - `LogOS/Apps/Irreversibility/BitResetLandauer.agda`
-- - `LogOS/Apps/Irreversibility/MeasurementCoarseGrainCompression.agda`
-- - guide: `docs/Patterns/Irreversible_Transformers.lagda.md`
--
-- Implemented now:
-- - the implemented surfaces are exactly the imports below
-- - detailed application narration lives in
--   `docs/Patterns/Irreversible_Transformers.lagda.md`
--
-- Planned:
-- - roadmap and next-step tracking live in external project planning docs

import LogOS.Apps.Irreversibility.BitReset
import LogOS.Apps.Irreversibility.BitResetDeutsch
import LogOS.Apps.Irreversibility.BitResetCompression
import LogOS.Apps.Irreversibility.BitResetLandauer
import LogOS.Apps.Irreversibility.MeasurementCoarseGrainCompression
