{-
LogOS: a host-minimal Agda library for modular dynamic logic systems synthesized by AI
Copyright (C) 2026 AI.IMPACT GmbH
SPDX-License-Identifier: GPL-3.0-only
-}

{-# OPTIONS --safe #-}
module LogOS.Apps.TuringCategory.All where

-- Turing category pack (implemented core).
--
-- Goal: express Cockett–Hofstra (2008) Turing categories in the LogOS
-- refinement-first discipline and connect them to observation-induced
-- partiality.
--
-- Entrypoints:
-- - `LogOS/Apps/TuringCategory/CH2008.agda` (interfaces)
-- - `LogOS/Apps/TuringCategory/PartialMaps.agda` (canonical partial-map model)
-- - `LogOS/Apps/TuringCategory/ParCH2008.agda` (CH2008 structure on the model)
-- - `LogOS/Apps/TuringCategory/ParTuring.agda` (packaging of a Turing object on `Par`)
-- - `LogOS/Apps/TuringCategory/ParTracked.agda` (Σ-totalisation / tracked partial maps)
-- - `LogOS/Apps/TuringCategory/Bridge.agda` and `Bridge/ObservationPrograms.agda`
-- - design note: `docs/Patterns/Partiality_Through_Observation.lagda.md`
--
-- Implemented now:
-- - the implemented surfaces are exactly the imports below
-- - detailed application narration lives in
--   `docs/Patterns/Partiality_Through_Observation.lagda.md`
--
-- Planned:
-- - roadmap and next-step tracking live in external project planning docs
--
-- Note: this is a convenience bundle for interactive navigation. We
-- deliberately avoid `public` re-exports in `LogOS/Apps/**` (Agda hygiene).
--
-- Design stance:
-- - everything is phrased over `Thin2Cat` (locally preordered 2-categories),
-- - laws are stated up to mutual refinement (`≈`), and
-- - “classical partial maps” live in a canonical Kleisli-style model.

open import LogOS.Apps.TuringCategory.CH2008 hiding (π₁; π₂; ⟨_,_⟩)
import LogOS.Apps.TuringCategory.PartialMaps
import LogOS.Apps.TuringCategory.ParCH2008
import LogOS.Apps.TuringCategory.ParTuring
import LogOS.Apps.TuringCategory.ParTracked
import LogOS.Apps.TuringCategory.Bridge
import LogOS.Apps.TuringCategory.Bridge.ObservationPrograms
