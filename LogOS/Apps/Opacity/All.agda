{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Opacity.All where

-- Opacity pack (implemented core with planned contract-facing extensions).
--
-- Goal: treat single-view information hiding as a clean slice of the same
-- boundary/contract discipline used elsewhere in the repo.
--
-- Entrypoints:
-- - `LogOS/Apps/Opacity/Demo.agda`
-- - `LogOS/Apps/Opacity/TagOpacity.agda`
-- - `LogOS/Ports/Opacity.agda`
-- - guide: `docs/Patterns/Opacity_Factorisation.lagda.md`
--
-- Implemented now:
-- - the implemented surfaces are exactly the imports below
-- - detailed application narration lives in
--   `docs/Patterns/Opacity_Factorisation.lagda.md`
--
-- Planned:
-- - roadmap and next-step tracking live in external project planning docs

import LogOS.Ports.Opacity as Opacity
import LogOS.Ports.Opacity.Port as OpacityPort
import LogOS.Apps.Opacity.Demo as Demo
import LogOS.Apps.Opacity.TagOpacity as TagOpacity
