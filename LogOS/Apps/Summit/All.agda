{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.Summit.All where

-- Summit capstone route (implemented apps-side surface).
--
-- Goal: collect the existing capstone theorem spines over a downstream logic
-- that is mechanisable in the strong apps-side sense: conservative
-- generalisation, quantitative cut structure, and compatible quoted
-- self-reference on the recognised fragment.
--
-- Entrypoints:
-- - `LogOS/Apps/Summit/Policy.agda`
-- - `LogOS/Apps/Summit/Recognition.agda`
-- - `LogOS/Apps/Summit/Mechanisable.agda`
-- - `LogOS/Apps/Summit/Admissibility.agda`
-- - `LogOS/Apps/Summit/Quantitative.agda`
-- - `LogOS/Apps/Summit/Obstruction.agda`
-- - `LogOS/Apps/Summit/Theorem.agda`
-- - result note: `docs/Results/Summit.lagda.md`
--
-- Implemented now:
-- - the implemented surfaces are exactly the imports below
-- - detailed theorem narration lives in `docs/Results/Summit.lagda.md`
--
-- Planned:
-- - roadmap and next-step tracking live in external project planning docs

import LogOS.Apps.Summit.Policy
import LogOS.Apps.Summit.Recognition
import LogOS.Apps.Summit.Mechanisable
import LogOS.Apps.Summit.Admissibility
import LogOS.Apps.Summit.Quantitative
import LogOS.Apps.Summit.Obstruction
import LogOS.Apps.Summit.Theorem
